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

: list-tail ( addr1 -- addr2 )
    begin
	dup @ dup while
	    nip list-next
    repeat
    drop ;

: list-insert { list addr -- }
    \ insert list at the start of the list pointed to by addr
    addr @ ( list2 )
    list addr !
    addr list-tail ! ;

\ constraint words

: trigger-constraints ( var -- )
    var-valconstraints @ triggered list-insert ;

: del-elem ( mask var -- )
    >r assert( dup singleton? )
    r@ var-set @ 2dup and if
	xor dup r@ var-set !
	dup 0= throw
	singleton? if
	    r@ trigger-constraints
	endif
    endif
    r> drop ;

: var-constraint ( var1 var2 -- var1 var2 )
    \ delete var1 element from var2, unless they are the same
	2dup <> if
	    over var-set @ over del-elem
	endif ;

: row-constraint ( var row -- )
    gridsize @ 0 ?do
	var-constraint var% %size +
    loop
    2drop ;

: col-constraint ( var col -- )
    gridsize @ 0 ?do
	var-constraint var% %size gridsize @ * +
    loop
    2drop ;

: box-constraint ( var box -- )
    boxsize @ 0 ?do
	dup >r
	boxsize @ 0 ?do
	    var-constraint var% %size +
	loop
	drop r> var% %size gridsize @ * +
    loop
    2drop ;

\ variable words

: set-variable ( u var -- )
    1 rot lshift over var-set !
    trigger-constraints ;

: make-vars { u -- }
    u dup * { vars }
    vars var% %size * allocate throw
    vars 0 ?do
	u full-set over var-set !
	0 over var-valconstraints !
	var% %size +
    loop
    grid ! ;

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

: propagate-constraints ( -- )
    begin
	triggered @ dup while
	    dup list-next @ triggered !
	    constraints-xt @ execute
    repeat
    drop ;


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
    c-addr u read-sudoku
    propagate-constraints
    u2 grid @ print-grid ;

: sudoku ( "name" -- )
    parse-name 9 sudoku-file ;

