(function () {
  "use strict";

  // Keep Unity's Brotli decoder and application data unchanged. Only reassemble the compressed download.
  window.createUnityInstanceWithSplitData = async function (canvas, config, onProgress) {
    const manifestUrl = new URL(config.dataUrl + ".parts.json", document.baseURI);
    const response = await fetch(manifestUrl, { cache: "no-cache" });
    if (!response.ok) throw new Error("Game data manifest could not be loaded (" + response.status + ").");
    const manifest = await response.json();
    if (manifest.version !== 1 || !Array.isArray(manifest.parts) || manifest.parts.length < 1 ||
        !Number.isSafeInteger(manifest.totalBytes) || manifest.totalBytes < 1)
      throw new Error("Invalid game data manifest.");

    const buffers = new Array(manifest.parts.length);
    const controller = new AbortController();
    let next = 0;
    let downloaded = 0;
    let objectUrl;
    const progress = (value) => { if (typeof onProgress === "function") onProgress(value); };
    progress(0);
    async function download() {
      while (next < manifest.parts.length) {
        const index = next++;
        const part = manifest.parts[index];
        const url = new URL(part.url, manifestUrl);
        if (url.origin !== manifestUrl.origin || url.pathname.slice(0, url.pathname.lastIndexOf("/") + 1) !==
            manifestUrl.pathname.slice(0, manifestUrl.pathname.lastIndexOf("/") + 1) ||
            !Number.isSafeInteger(part.bytes) || part.bytes < 1 || !/^[a-f0-9]{64}$/.test(part.sha256))
          throw new Error("Invalid game data part.");
        const result = await fetch(url, { cache: "force-cache", signal: controller.signal });
        if (!result.ok) throw new Error("Game data download failed: " + part.url + " (" + result.status + ").");
        const data = await result.arrayBuffer();
        if (data.byteLength !== part.bytes) throw new Error("Incomplete game data: " + part.url);
        if (window.crypto && window.crypto.subtle) {
          const digest = new Uint8Array(await window.crypto.subtle.digest("SHA-256", data));
          const hash = Array.from(digest, (value) => value.toString(16).padStart(2, "0")).join("");
          if (hash !== part.sha256) throw new Error("Game data verification failed: " + part.url);
        }
        buffers[index] = data;
        downloaded += data.byteLength;
        progress(0.5 * downloaded / manifest.totalBytes);
      }
    }
    try {
      await Promise.all(Array.from({ length: Math.min(2, manifest.parts.length) }, download));
      if (downloaded !== manifest.totalBytes) throw new Error("Incomplete game data download.");
      objectUrl = URL.createObjectURL(new Blob(buffers, { type: "application/octet-stream" }));
      buffers.fill(null);
      const previousCacheControl = config.cacheControl;
      const prepared = Object.assign({}, config, {
        dataUrl: objectUrl,
        // The immutable part URLs use the browser cache; do not persist a new temporary blob URL every visit.
        cacheControl: function (url) {
          return url === objectUrl ? "no-store" :
            (typeof previousCacheControl === "function" ? previousCacheControl(url) : "no-store");
        }
      });
      return await window.createUnityInstance(canvas, prepared, (value) => progress(0.5 + value * 0.5));
    } catch (error) {
      controller.abort();
      throw error;
    } finally {
      if (objectUrl) URL.revokeObjectURL(objectUrl);
    }
  };
})();
