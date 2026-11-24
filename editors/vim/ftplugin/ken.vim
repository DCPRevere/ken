" Ken: indentation-based, comments start with #
if exists("b:did_ftplugin") | finish | endif
let b:did_ftplugin = 1
setlocal commentstring=#\ %s
setlocal comments=:#
setlocal expandtab shiftwidth=2 softtabstop=2
compiler ken
" :make checks the current file and fills the quickfix list
