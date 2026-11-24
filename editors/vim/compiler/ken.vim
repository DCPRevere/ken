if exists("current_compiler") | finish | endif
let current_compiler = "ken"
CompilerSet makeprg=ken\ check\ --quiet\ %
" error FILE:LINE [@ e2]: message   /   warning FILE:LINE: message
CompilerSet errorformat=%trror\ %f:%l\ %m,%trror\ %f:%l:\ %m,%tarning\ %f:%l\ %m,%tarning\ %f:%l:\ %m,%trror:\ %f:%l:\ %m,%-G%.%#
