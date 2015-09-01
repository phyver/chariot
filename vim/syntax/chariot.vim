" Vim syntax file
" Language: chariot
" Maintainer: Pierre Hyvernat
" Latest Revision: 21 Jul 2015

if exists("b:current_syntax")
  finish
endif

syntax keyword chKeyword val type and where
syntax keyword chData data codata
syntax match chInt '\<\d\+\>'
syntax match chConst '\<[A-Z][a-zA-Z0-9_]*\>'
syntax match chAngel "???"
syntax match chTVar '\'[a-z][a-zA-Z0-9_]*\>'

syn region chComment start="(\*" end="\*)" contains=chComment
syn match chComment '--.*'
syn match chComment '….*'

syn match chCommand '^\s*:.\+'




hi def link chKeyword Keyword
hi def link chData Typedef

hi def link chInt Constant
hi def link chConst Constant
hi def link chAngel Constant

hi def link chCommand Macro

hi def link chComment Comment
hi def link chTVar Type


let b:current_syntax = "chariot"

