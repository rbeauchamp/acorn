import Acorn.Host.Viewer.BrowserKernel

def _root_.NativeApp.BrowserKernel.main : IO Unit := do
  (← IO.getStdout).putStr Acorn.Host.Viewer.browserKernelJavascript
