/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.HttpServer
import Acorn.Host.Viewer.BrowserSchema

/-!
# Compiled observer resources

The native build dependency includes the maintained observer resource. Historical
study records are outside the live observer HTTP surface.
-/
namespace NativeApp

/-- Fixed compiled resource ownership; HTTP accepts no filesystem path from a request. -/
def viewerAssets : Acorn.Host.Viewer.ViewerAssets where
  index := (include_str "../../viewer/static/index.html").replace
    "/* LEAN_BROWSER_KERNEL */" Acorn.Host.Viewer.browserKernelJavascript

end NativeApp
