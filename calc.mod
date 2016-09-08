bracket Pre G Post :- print Pre, term_to_string G S, print S, print Post.
announce G :- bracket ">>" G "\n", fail.
spy G :- (bracket ">Entering " G "\n", G, bracket ">Success  " G "\n";
          bracket ">Leaving  " G "\n",  fail).



%nf A B :- (bnf A A, A = B) ; ( bnf A C, nf C B). 
nf A A :- bnf A A, ! .
nf A B :- bnf A C , nf C B .

%bnf A B :- announce ( bnf A B).
bnf X XX :- defs X XX _.
bnf (app (ast T F) N) (FF) :-    !, bnf (F N) FF. %print "-|1|-\n",
bnf (app M N) (app MM NN) :-        bnf M MM, bnf N NN.
bnf (ast T F) (ast T FF) :-    pi X\(of X T, bnf X X ) => bnf (F X) (FF X).

conv A B :- bnf A C, bnf B C.

of X Y :- defs X _ Y.
of (app N M) B :- of M A, of N (arr A B).
of (ast T F) (arr T S) :- pi X\ (of X T, bnf X X) => (of (F X) S).
of (lamda A F) (setPi A B) :- pi X\ (of X A, bnf X X) => (of (F X) (B X)).
of (apply F E) BE :- of E Ai, of F (setPi A B), conv A Ai, BE = B E.
of (id Aa) (setId A Aa Aa) :- of Aa A.
% of (id Aa) (setId A Aa Ab) :- of Aa A, of Ab A, conv Aa Ab.    


isType nat.
isType (arr X Y) :- isType X, isType Y.
isType (setPi A B) :- isType A, pi X\ (of X A, bnf X X) => isType (B X).
isType (setId A Aa Ab) :- isType A, of Aa A, of Ab A.

load_library [] GOAL :- GOAL.
load_library [ddd NAME BODY | TAIL ] GOAL :-
 of BODY TYPE,
 defs NAME BODY TYPE => load_library TAIL GOAL.

defs succ (ast T N\ (ast (arr Gamma Gamma) F\ (ast Gamma X\ (app F ( app (app N F) X))))).
defs zero (ast (arr nat nat) F\ ast nat X\X).
defs nrec (ast nat F\ ast nat K\ ast nat N\ app (app N F) K ).


defs id   (ast nat X\X).
defs asd  (ast nat Y\ ast nat X\  app Succ (app Y X)) :- defs succ Succ.
defs plus ( app (app (app R F) Id) (ast nat X\app Succ X ) ) :- defs succ Succ, defs zero Zero, defs id Id, defs nrec R.
defs mult ( app (app (app R F) (ast nat X\Zero)) (app Succ Zero ) ) 
    :- 
    defs succ Succ, 
    defs zero Zero, 
    defs id Id, 
    defs nrec R.
    


k1 Q :- defs plus Plus, 
            intnat 10 N,
            intnat 20 M,
            nf ( app ( app (Plus) ( N ) ) M ) Q.





%intnat2 A B :- announce ( intnat A B).
intnat2 0 Zero :- defs zero Zero.
intnat2 K (app Succ N) :- 
    defs succ Succ, 
    K > 0, KK is K - 1, 
    intnat2 KK N.
intnat A B :- intnat2 A Q, nf Q B.

%natint A B :- announce ( natint A B).
natint Zero 0 :- defs zero Zero, !.
natint Q N :- 
     defs succ Succ
    ,nf Q A
    ,nf (app Succ QQ) B
    
    ,A = B 
    ,print "\n2\n"
%    natint QQ NN,
    %term_to_string NN S, print "\n\n", print S, print "\n\n",
%    N is NN + 1
    .




%bnf (app (ast T F) N) (FN) :- print "-|1|-",    of  N T,    print " -1.1-\n",    bnf (F N) FN.
%bnf (app M N) (app MM NN) :- print "-|2|-\n",   of N A,    of M (arr A B),    bnf M MM, bnf N NN.
%bnf (ast T F) (ast T FF) :- print "-|3|-\n",    ((bnf X X) => (bnf (F X) (FF X))).




%of zero nat.
%of succ (arr nat nat).

%of (ast (arr T T) F\ ast T X\X) nat.  
%of ( ast nat N\  ast (arr T T) F\ ast T X\ app F ( app (app N F) X) ) (arr nat nat).

%of A B :- spy( of A B).
%
%k2 Q :- bnf (app (ast nat N\ (ast nat F\ (ast nat X\ (app F ( app (app N F) X))))) (ast nat F\ ast nat X\X) ) Q.
%k3 Q :- bnf (ast nat X\ ast  nat Y\ ast nat Z\ app X (app (app Y Y) Z) ) Q.


is_ast (ast A B).
is_app (app A B).


nfable (app A B) :- !, (is_ast A ; nfable A ; nfable B).
nfable (ast A B) :- !, pi X\ nfable ( B X ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%TESTS
defs twat (app (app (app (app (app (app(app(app(ast nat x1\ ast nat x2\ ast nat x3\ ast nat x4\ ast nat x5\ ast nat x6\ x6) (ast nat x\x))(ast nat x\x))(ast nat x\x))(ast nat x\x))(ast nat x\x))(ast nat x\x))(ast nat x\x))(ast nat x\x)).





