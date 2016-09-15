bracket Pre G Post :- print Pre, term_to_string G S, print S, print Post.
announce G :- bracket ">>" G "\n", fail.
spy G :- (bracket ">Entering " G "\n", G, bracket ">Success  " G "\n";
          bracket ">Leaving  " G "\n",  fail).


%fixpoint F A A :- F A A, !.
%fixpoint F A B :- F A C, fixpoint F C B.

% nf === fixpoint bnf
nf A B :- announce ( nf A B).
nf A A :- bnf A A, ! .
nf A B :- bnf A C , nf C B .

%bnf X XX :- defs X XX _.
bnf A B :- announce (bnf A B).
%bnf X X :- is_const X ; is_canon X.
bnf (app (ast T F) N) (FF) :-    !, bnf (F N) FF. %print "-|1|-\n",
bnf (app M N) (app MM NN) :-        bnf M MM, bnf N NN.
bnf (ast T F) (ast T FF) :-    pi X\(of X T, bnf X X ) => bnf (F X) (FF X).

of X Y :- defs X _ Y.


%%% nat computation rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%                    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%                        
is_canon zero.  is_canon succ.  is_const nrec.

bnf (nrec F K zero) K         :-  print "\n$bnf nrec 0$".
bnf (nrec F K (succ n)) (F n (nrec F K n)) :-  print "\n$bnf nrec succ$" .

bnf (succ E) (succ Q) :- bnf E Q.

isType nat.

%defs uno (succ zero) nat.
%defs due (succ zero) nat.

defs plus (m\ nrec succ m).
defs prec ( nrec (x\x) zero). 

of zero nat.
of (succ A) nat :- of A nat.

conv A B :- nf A B ; (nf A C, nf B C).




 


                                                                 %%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%                    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

load_library [] GOAL :- GOAL.
load_library [ddd NAME BODY | TAIL ] GOAL :-
 of BODY TYPE,
 defs NAME BODY TYPE => load_library TAIL GOAL.



intnat 0 zero.
intnat K (succ N) :- 
    K > 0, KK is K - 1, 
    intnat KK N.


natint A B :- announce ( natint A B).

natint zero 0 :- !.
natint Nat Int :-
    defs prec Prec,
    conv (Prec Nat) A,
    print "\n11\n11\n",
    natint A Int2,
    Int is Int2 +1
    .

isType (arr X Y) :- isType X, isType Y.
isType (setPi A B) :- isType A, pi X\ (of X A, bnf X X) => isType (B X).
isType (setId A Aa Ab) :- isType A, of Aa A, of Ab A.

of (app N M) B :- of M A, of N (arr A B).
of (ast T F) (arr T S) :- pi X\ (of X T, bnf X X) => (of (F X) S).
of (lamda A F) (setPi A B) :- pi X\ (of X A, bnf X X) => (of (F X) (B X)).
of (apply F E) BE :- of E Ai, of F (setPi A B), conv A Ai, BE = B E.
of (id Aa) (setId A Aa Aa) :- of Aa A.
% of (id Aa) (setId A Aa Ab) :- of Aa A, of Ab A, conv Aa Ab.    

