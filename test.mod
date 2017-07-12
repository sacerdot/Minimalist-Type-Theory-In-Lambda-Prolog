

trad A B    :- announce (trad A B).
tau A B C D :- announce (tau A B C D).
tau' A B C  :- announce (tau' A B C).
hnf A B     :- announce (hnf A B).
hstep A B   :- announce (hstep A B).
dstep A B   :- announce (dstep A B).
nf A B      :- announce (nf A B).
conv A B    :- announce (conv A B).
of A B IE   :- announce (of A B IE).

isType A K  :- announce (isType A K).
isa BB B IE :- announce (isa BB B IE).
sigm A B D  :- announce (sigm A B D).
equ T A B O :- announce (equ T A B O).
macro A B   :- announce (macro A B).


nf A B :- announce (nf A B).
hstep A B :- announce (hstep A B).
conv A B :- announce ( conv A B).
testB A :- announce (testB A).
hstep A B :- announce (hstep A B).

hstep X N
    :-  locDef X T M
    ,   conv M N
    .

testB X
    :-  (locDef X singleton star) => nf (elim_singleton star (x\ singleton) star) X.




of (letIn (locDef X T M) N) T' IE
    :-  locDef X T M
    =>  of N T' IE
    .

of X T IE :- locDef X T M.



hstep (letIn (locDef X T M) N) N'
    :-  locDef X T M
    =>  conv N' N.
    



