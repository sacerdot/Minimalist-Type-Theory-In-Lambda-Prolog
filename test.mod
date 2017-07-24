


bracket Pre G Post :- print Pre, term_to_string G S, print S, print Post.
announce G :- bracket ">>" G "\n", fail.
spy G :- bracket "[--[Entering " G "\n", G, bracket "]--]Success  " G "\n".
spy G :- not G, bracket "]--]Leaving  " G "\n",  fail.

printt A :- term_to_string A S, print S.
println A :- printt A, print "\n".
printW S A :- print S, printt A, print "\n".

load_library [] GOAL :- GOAL.
load_library [ddd NAME BODY | TAIL ] GOAL :-
 of BODY TYPE int,
 defs NAME BODY TYPE => load_library TAIL GOAL.

test_library [].
test_library [Test | Tail] :- Test , test_library Tail.

/*
trad A B    :- announce (trad A B).
tau A B C D :- announce (tau A B C D).
tau' A B C  :- announce (tau' A B C).
hnf A B     :- announce (hnf A B).
hstep A B   :- announce (hstep A B).
dstep A B   :- announce (dstep A B).
nf A B      :- announce (nf A B).
conv A B    :- announce (conv A B).
of A B IE   :- announce (of A B IE).

isType A K IE :- announce (isType A K IE).
isa BB B IE :- announce (isa BB B IE).
sigm A B D  :- announce (sigm A B D).
equ T A B O :- announce (equ T A B O).
macro A B   :- announce (macro A B).


of A B :- announce (of A B).

nf A B :- announce (nf A B).
hstep A B :- announce (hstep A B).
conv A B :- announce ( conv A B).
testB A :- announce (testB A).
hstep A B :- announce (hstep A B).
*/





isType (forall B C) prop ext :-
        println "--forall------"
    ,   (pi x\ locDecl x B => isType (C x) prop ext)
    .

isType (implies B C) prop ext :-
        println "--implies-----\n\n\n\n\n\n\n"
    ,   isType B prop ext
    ,   isType C prop ext
    .

isType (propEq TypeC C1 C2) prop ext:-
        println "--propEq------"
    ,   isType TypeC col ext
    ,   print "-.-.-.-." , println TypeC
    ,   spy (of C1 TypeC ext)
    ,   println "--first-spy-done"
    ,   spy (of C2 TypeC ext)
    .




accumulate calc_Eq.

accumulate calc_setPi.

accumulate calc_singleton.

accumulate main.

testC
    :-  Long = (
        forall singleton x\
         forall singleton y\
          forall (propEq singleton x star) l\
           forall (setPi (propEq singleton y star) z\ singleton) f\
            forall (propEq singleton x y) h\
                (propEq singleton (apply f l) star)
            )
    ,   println Long
    ,   isType Long prop ext
    .


testExt
    :-  Dom = singleton
    ,   println Dom
    ,   Long = (
        forall Dom x\
         forall Dom y\
          forall (propEq Dom x x) l\
           forall (setPi (propEq Dom y y) z\ Dom) f\
            implies (propEq Dom x y) (propEq Dom (apply f l) (apply f l))
            )
    ,   println Long
    ,   isType Long prop ext
    .


testshort Q :-
        Dom = singleton
    ,   Short = (
         forall Dom y\
          forall singleton l\
           forall (setPi singleton z\Dom) f\
            (propEq Dom (apply f l) (apply f l))
            )
    ,   isType Short Q ext
    .

test sostituzione_diretta :- locDecl h (propEq singleton qwe star) => dstep qwe A.
test sostituzione_indiretta :- (dstep a b :- locDef _ (propEq _ a b) _ ) .


