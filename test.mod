
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


nf A B :- announce (nf A B).
hstep A B :- announce (hstep A B).
conv A B :- announce ( conv A B).
testB A :- announce (testB A).
hstep A B :- announce (hstep A B).



testB X :- (locDef X singleton star) => nf (elim_singleton star (x\ singleton) star) X.




of (letIn (locDef X T M) N) T' IE
    :-  locDef X T M
    =>  of N T' IE
    .

of X T IE :- locDef X T M.



hstep (letIn (locDef X T M) N) N'
    :-  locDef X T M
    =>  conv N' N.



testExt
    :-  Dom = singleton
    ,   println Dom
    ,   Long =  (
        forall Dom x\
         forall Dom y\
          forall (propEq Dom x x) l\
           forall (propEq Dom y y) f\
            implies (propEq Dom x y) (propEq Dom (apply f l) (apply f l))
            )
    ,   println Long
    ,   isType Long prop ext
    .



isType (forall B C) prop ext :-
        println "--forall------"
    ,   (pi x\ of x B ext => isType (C x) prop ext)
    .

isType (implies B C) prop ext :-
        println "--implies-----"
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

isType singleton set ext.
isType A col ext :- isType A set ext.
isType A set ext :- isType A prop ext.

of (apply F X) (CX) ext :-
        of X B ext
    ,   print "------------\n--- printing the type of the domain of f: ", println (of X B ext)
    ,   spy (of F (setPi B C) ext)
    ,   print "------------\n--- printing the type of the codomain of f: ", println (of F (setPi B C))
    ,   print "------------\n--- printing the type of f: ", println F
    ,   CX = C X
    .

of (lambda B F) (setPi B C) ext :-
        print "---------of-lambdas-", println (of (lambda B F) (setPi B C) ext)
    ,   isType B set ext
    ,   spy (pi x\ of x B ext => of (F x) (C x) ext)
    ,   spy (pi x\ of x B ext => isType (C x) set ext)
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



isType (propEq A AA1 AA2) propS ext :-
    isa AA1 A ext,
    isa AA2 A ext,
    isType A set ext.

isType (propEq A AA1 AA2) prop ext :-
    isa AA1 A ext,
    isa AA2 A ext,
    isType A col ext.


of (eqTrue C Cc) (propEq C Cc Cc) ext
    :-  of Cc C ext
    .


conv A B :- of _ (propEq _ A B).

conv A B :- locDef _ (propEq _ A B) _ .


