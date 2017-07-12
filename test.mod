


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
    



accumulate calc_singleton.
accumulate main.


