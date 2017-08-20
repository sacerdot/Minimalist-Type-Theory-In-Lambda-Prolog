
%locDef X T M
%letIn lDef N



%locDef X T M
%letIn T M N
letIn (locDef T M) N %con N di tipo funzione

of (letIn (locDef X T M) N) T' IE
    :-  locDef X T M
    =>  of N T' IE
    .

%of (letIn _ M N) T IE :- of (N M) T IE.


of X T IE :- locDef X T M.
% idem


%hstep X N
%    :-  locDef X T M
%    ,   conv M N
%    .

hstep X N
    :-  locDef X T N
    .

hstep (letIn (locDef X T M) N) N'
    :-  locDef X T M
    =>  conv N N'
    .
%hstep (letIn T M N) (N M).




