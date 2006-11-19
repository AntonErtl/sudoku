\ constraint-based sudoku solver (and maybe later more), by Anton Ertl

\ Usage:

\ To solve a 9x9 Sudoku with the start values residing in <file>
\ gforth sudoku.fs -e "sudoku <file> bye"

\ File format: a digit or letter for each filled square, and something
\ else (but not a control character) for a non-filled square; control
\ characters are ignored; don't do trailing spaces

\ 0.6.2 compatibility

: parse-name parse-word ;

\ linked list
struct
    cell% field list-next
end-struct list%

\ constraint list
list%
    cell% field constraints-xt
end-struct constraints%

\ constraint variable
struct
    cell% field var-set            \ set of possible values in the variable
    cell% field var-valconstraints \ constraints triggered on value
end-struct var%

variable triggered \ constraints that have been triggered

variable grid  \ n*n vars

variable gridsize
variable boxsize

\ gridsize arrays of gridsize vectors; element[m][n] counts in how
\ many places the digit n can still occur in the container m
variable row-counts
variable col-counts
variable box-counts

\ set words

: singleton? ( set -- f )
    \ does the set have one element?
    assert( dup 0<> )
    dup 1- and 0= ;

: element-num ( set -- n )
    \ if the set has only one element, n is its number, otherwise n=-1
    0 begin
	over 1 and if
	    swap 1 <> if
		drop -1
	    endif
	    exit
	endif
	1+ swap 1 rshift swap
    over 0= until
    2drop -1 ;

: full-set ( u -- set )
    \ set with u elements, all set
    1 swap lshift 1- ;

: singleton ( u -- set )
    1 swap lshift ;

\ list words

: list-insert { list addr -- }
    addr @ list list-next !
    list addr ! ;

: list-tail ( addr1 -- addr2 )
    begin 
	dup @ dup while
	    nip list-next
    repeat
    drop ;

: list-concat { list addr -- }
    \ insert list at the start of the list pointed to by addr
    addr @ ( list2 )
    list addr !
    addr list-tail ! ;

\ walkers

: do-row ( compilation: -- do-sys; run-time: row -- row-elem R: row-elem )
    ]] gridsize @ 0 ?do dup >r [[ ; immediate

: loop-row ( compilation: -- do-sys; run-time: R: row-elem -- )
    ]] r> var% %size + loop drop [[ ; immediate

: do-col ( compilation: -- do-sys; run-time: col -- col-elem R: col-elem )
    ]] gridsize @ 0 ?do dup >r [[ ; immediate

: loop-col ( compilation: -- do-sys; run-time: R: col-elem -- )
    ]] r> var% %size gridsize @ * + loop drop [[ ; immediate

: do-box ( compilation: -- do-sys; run-time: box -- box-elem R: box-elem )
    ]] boxsize @ 0 ?do dup >r
	boxsize @ 0 ?do dup >r [[ ; immediate

: loop-box ( compilation: -- do-sys; run-time: R: box-elem -- ) 
    ]] r> var% %size + loop drop r> var% %size gridsize @ * + loop drop [[
; immediate

: do-boxes ( compilation: -- do-sys; run-time: grid -- box R: box )
    ]] boxsize @ 0 ?do dup >r
	boxsize @ 0 ?do dup >r [[ ; immediate

: loop-boxes ( compilation: -- do-sys; run-time: R: box -- )
    ]] r> var% %size boxsize @ * + loop drop
       r> var% %size gridsize @ boxsize @ * * + loop drop [[ ; immediate

: cont-i ( -- n )
    \ container index
    ]] r> i swap >r [[ ; immediate

\ constraint execution

: trigger-constraints ( var -- )
    var-valconstraints @ triggered list-concat ;

: del-elem ( mask var -- )
    >r assert( dup singleton? )
    r@ var-set @ 2dup and if
	xor dup r@ var-set !
	dup 0= throw
	singleton? if
	    r@ trigger-constraints
	endif
    else
	2drop
    endif
    r> drop ;

: var-constraint ( var1 var2 -- var1 var2 )
    \ delete var1 element from var2, unless they are the same
    2dup <> if
	over var-set @ over del-elem
    endif ;

: var-constraint1 ( var1 var2 -- var1 )
    var-constraint drop ;

: row-constraint ( var row -- )
    do-row var-constraint drop loop-row drop ;

: col-constraint ( var col -- )
    do-col var-constraint drop loop-col drop ;

: box-constraint ( var box -- )
    do-box var-constraint drop loop-box drop ;

: propagate-constraints ( -- )
    begin
	triggered @ dup while
	    dup list-next @ triggered !
	    constraints-xt @ execute
    repeat
    drop ;

\ constraint creation

: gen-valconstraint { var container xt -- }
    constraints% %size allocate throw >r 
    :noname
    var       postpone literal
    container postpone literal
    xt compile,
    postpone ;
    r@ constraints-xt !
    r> var var-valconstraints list-insert ;

: check ( -- )
    triggered list-tail drop
    grid @
    gridsize @ dup * 0 ?do
	dup var-valconstraints list-tail drop
	var% %size +
    loop
    drop ;

: gen-valconstraint1 { xt container var -- xt container }
    var container xt gen-valconstraint
    xt container
    check ;

: gen-contconstraint { xt-map xt-constraint container -- xt-map xt-constraint }
    xt-map xt-constraint container dup ['] gen-valconstraint1 xt-map execute
    drop ;

: gen-row-constraints ( -- )
    check
    grid @ do-col
	dup do-row
	    over ['] row-constraint gen-valconstraint check
	loop-row
	drop
    loop-col ;

: gen-col-constraints ( -- )
    check
    grid @ do-row
	dup do-col
	    over ['] col-constraint gen-valconstraint check
	loop-col
	drop
    loop-row ;

: gen-box-constraints ( -- )
    check
    grid @ do-boxes
	dup do-box
	    over ['] box-constraint gen-valconstraint check
	loop-box
	drop
    loop-boxes ;

: gen-constraints
    gen-row-constraints
    gen-col-constraints
    gen-box-constraints ;


\ counting potential values

: gen-counts ( -- addr )
    gridsize @ dup * dup chars allocate throw dup
    rot 0 ?do
        gridsize @ over c!
        char+ loop
    drop ;

: init-counts ( -- )
    gen-counts row-counts !
    gen-counts col-counts !
    gen-counts box-counts ! ;

: var-set? ( var n -- f )
    1 swap lshift swap @ and 0<> ;

: check-rowcounts-digit ( n -- )
    { digit } grid @ do-col
	0 swap do-row
	    digit var-set? -
	loop-row
	cont-i chars row-counts @ + c@ <> throw
    loop-col ;

: check-colcounts-digit ( n -- )
    { digit } grid @ do-row
	0 swap do-col
	    digit var-set? -
	loop-col
	cont-i chars col-counts @ + c@ <> throw
    loop-row ;

: check-boxcounts-digit ( n -- )
    { digit } grid @ do-boxes
	0 swap do-box
	    digit var-set? -
	loop-box
	cont-i chars box-counts @ + c@ <> throw
    loop-boxes ;

: check-counts ( -- )
    gridsize @ 0 ?do
	i check-rowcounts-digit
	i check-colcounts-digit
	i check-boxcounts-digit
    loop ;



\ variable words

: set-variable ( u var -- )
    1 rot lshift over var-set !
    trigger-constraints ;

: make-vars { u -- }
    u dup * { vars }
    vars var% %size * allocate throw dup grid !
    vars 0 ?do
	u full-set over var-set !
	0 over var-valconstraints !
	var% %size +
    loop
    drop
    check ;

\ file reading

: sudoku-char? ( c -- u|c f )
    dup '1 '9 1+ within if
	'1 - true exit
    endif
    toupper dup 'A 'Z 1+ within if
	'A - 9 + true exit
    endif
    false ;

: read-sudoku ( c-addr u -- )
    slurp-file grid @ -rot bounds ?do
	i c@ sudoku-char? if
	    over set-variable
	    'a \ a dummy non-control character
	endif
	bl >= if
	    var% %size +
	endif
    loop
    drop ;

\ printing

: print-var ( var -- )
    var-set @ element-num dup 0< if
	drop bl
    else
	'1 + dup '9 > if
	    7 +
	endif
    endif
    emit ;

: print-grid { u addr -- }
    \ print u*u grid at addr
    addr u 0 ?do
	i boxsize @ mod 0= i 0> and if
	    cr
	    u 0 ?do
		i boxsize @ mod 0= i 0> and if
		    '+ emit
		endif
		'- emit
	    loop
	endif
	cr
	u 0 ?do
	    i boxsize @ mod 0= i 0> and if
		'| emit
	    endif
	    dup print-var
	    var% %size +
	loop
    loop
    drop cr ;

: sudoku-file { c-addr u u2 -- }
    \ solve u2*u2 sudoku from file c-addr u
    u2 s>d d>f fsqrt f>d drop boxsize !
    u2 gridsize !
    u2 make-vars
    init-counts
    check-counts 
    gen-constraints
    c-addr u read-sudoku
    propagate-constraints
    u2 grid @ print-grid ;

: sudoku ( "name" -- )
    parse-name 9 sudoku-file ;

\ Local Variables:
\ forth-local-indent-words: ((("do-row" "do-col" "do-box") (0 . 2) (0 . 2)) (("loop-row" "loop-col" "loop-box") (-2 . 0) (0 . -2)))
\ forth-local-words: ((("do-row" "do-col" "do-box" "loop-row" "loop-col" "loop-box") compile-only (font-lock-keyword-face . 2)))
\ End:
