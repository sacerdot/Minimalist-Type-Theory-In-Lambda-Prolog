bracket Pre G Post :- print Pre, term_to_string G S, print S, print Post.
announce G :- bracket ">>" G "\n", fail.
spy G :- (bracket ">Entering " G "\n", G, bracket ">Success  " G "\n";
          bracket ">Leaving  " G "\n",  fail).


%fixpoint F A A :- F A A, !.
%fixpoint F A B :- F A C, fixpoint F C B.

% nf === fixpoint bnf
nf A A :- bnf A A, ! .
nf A B :- bnf A C , nf C B .

bnf X XX :- defs X XX _.
bnf X X :- is_const X.
bnf (app (ast T F) N) (FF) :-    !, bnf (F N) FF. %print "-|1|-\n",
bnf (app M N) (app MM NN) :-        bnf M MM, bnf N NN.
bnf (ast T F) (ast T FF) :-    pi X\(of X T, bnf X X ) => bnf (F X) (FF X).

%%% nat computation rules
is_const zero.
is_const succ.
is_const nrec.
is_canon zero.
is_canon succ.

bnf (nrec F K zero) K.
bnf (nrec F K (succ n) (F n (nrec F K n)).

isType nat.

of zero nat.
of (succ A) nat :- of A nat.

conv A B :- bnf A C, bnf B C.

of X Y :- defs X _ Y.
of (app N M) B :- of M A, of N (arr A B).
of (ast T F) (arr T S) :- pi X\ (of X T, bnf X X) => (of (F X) S).
of (lamda A F) (setPi A B) :- pi X\ (of X A, bnf X X) => (of (F X) (B X)).
of (apply F E) BE :- of E Ai, of F (setPi A B), conv A Ai, BE = B E.
of (id Aa) (setId A Aa Aa) :- of Aa A.
% of (id Aa) (setId A Aa Ab) :- of Aa A, of Ab A, conv Aa Ab.    

isType (arr X Y) :- isType X, isType Y.
isType (setPi A B) :- isType A, pi X\ (of X A, bnf X X) => isType (B X).
isType (setId A Aa Ab) :- isType A, of Aa A, of Ab A.

load_library [] GOAL :- GOAL.
load_library [ddd NAME BODY | TAIL ] GOAL :-
 of BODY TYPE,
 defs NAME BODY TYPE => load_library TAIL GOAL.



intnat 0 zero.
intnat K (succ N) :- 
    K > 0, KK is K - 1, 
    intnat KK N.


%natint A B :- announce ( natint A B).
natint Zero 0 :- defs zero Zero, !.
natint Q N :- 
     defs succ Succ
    ,nf Q A
    ,nf (app Succ QQ) B
    
    ,A = B 
.


