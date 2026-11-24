import Acorn.Host.Viewer.HttpServer
import Acorn.Host.Viewer.BrowserKernel

namespace NativeApp

def viewerAssets : Acorn.Host.Viewer.ViewerAssets where
  index := (include_str "../../viewer/static/index.html").replace
    "/* LEAN_BROWSER_KERNEL */" Acorn.Host.Viewer.browserKernelJavascript

end NativeApp
