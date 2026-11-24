" Vim syntax file for Ken (.ken)
if exists("b:current_syntax") | finish | endif

syn match   kenComment   "\(^\|\s\)#.*$" contains=kenTodo
syn keyword kenTodo      TODO FIXME XXX contained
syn keyword kenDecl      world about revises from given agent type fact action rule private timeline expect use invariant
syn keyword kenDecl      allow bootstrap
syn match   kenDecl      "\<time travel\>"
syn keyword kenClause    needs effect seen by everyone nobody every where as hiding secretly except then for in
syn keyword kenClause    may happen unseen
syn keyword kenRule      after sees when do
syn keyword kenBelief    concludes because despite suspects forgets watches wants knows believes whether saw
syn match   kenBelief    "\<so that\>"
syn match   kenBelief    "\<no longer \(wants\|watches\)\>"
syn match   kenBelief    "\<common knowledge\>"
syn match   kenBelief    "\<deducible by\>"
syn match   kenBelief    "\<possible for\>"
syn keyword kenOp        not and or all some
syn keyword kenTime      at before throughout start end overwrite branching fixed
syn keyword kenMode      person logician
syn keyword kenConst     true false
syn match   kenNumber    "\<\d\+\>"
syn match   kenLabel     "^\s\+\zs[A-Za-z_][A-Za-z0-9_]*\ze\s*\(@\s*\d\+\s*\)\?:"
syn match   kenStamp     "@\s*\d\+"
syn match   kenSym       "=>\|<=>\|!=\|<=\|>="

hi def link kenComment Comment
hi def link kenTodo    Todo
hi def link kenDecl    Keyword
hi def link kenClause  Statement
hi def link kenRule    Conditional
hi def link kenBelief  Special
hi def link kenOp      Operator
hi def link kenSym     Operator
hi def link kenTime    Type
hi def link kenMode    Type
hi def link kenConst   Constant
hi def link kenNumber  Number
hi def link kenLabel   Label
hi def link kenStamp   Number

let b:current_syntax = "ken"
