
%locDef X T M

%letIn lDef N

of (letIn (locDef T M) N) T' IE
    :-  locDef X T M
    =>  of N T' IE
    .

of X T IE :- locDef X T M.

hstep A B :- announce (hstep A B).
hstep X N
    :-  locDef X T M
    ,   conv M N
    .

hstep (letIn (locDef X T M) N) N'
    :-  locDef X T M
    =>  conv N N'
    .

letIn (locDef T M) N %con N di tipo funzione
