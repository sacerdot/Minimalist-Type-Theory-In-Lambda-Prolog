%%-- main.elpi


bracket Pre G Post :- print Pre, term_to_string G S, print S, print Post.
announce G :- bracket ">>" G "\n", fail.
spy G :- (bracket "[--[Entering " G "\n", G, bracket "]--]Success  " G "\n";
          bracket "]--]Leaving  " G "\n",  fail).

printt A :- term_to_string A S, print S.
printW S A :- print S, printt A, print "\n".

load_library [] GOAL :- GOAL.
load_library [ddd NAME BODY | TAIL ] GOAL :-
 of BODY TYPE int,
 defs NAME BODY TYPE => load_library TAIL GOAL.

test_library [].
test_library [Test | Tail] :- Test , test_library Tail.


% non contextual, non reflexive, maybe transitive closure
% hstep A B

% non contextual, transitive, reflexive normal form
hnf A B :- hstep A C, !, hnf C B.
hnf A A.
% contextual, non reflexive, maybe transitive closure
dstep A B :- hstep A B.

% contextual, transitive, reflexive normal form
nf A B :- dstep A C, !, nf C B.
%nf A A :- printW "HO TROVATO UNA FORMA NORMALE: "  A.
nf A A.
conv A A :- ! .
conv A B :- nf A C, nf B C.


isType A col B  :- isType A set   B.
isType A col B  :- isType A prop  B.
isType A set B  :- isType A props B.
isType A prop B :- isType A props B.

isa Term TY IE :-
    of Term TY' IE,
    conv TY TY'.

%tau Tipo_di_partenza Tipo_di_arrivo Input Output :- fail.

tau' TipoExt ElementoExt Output :-
    trad ElementoExt ElementoInt,
    trad TipoExt TipoInt,
    of ElementoInt Ty int,
    tau Ty TipoInt ElementoInt Output.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Is this ever needed?
%trad (of Aa AA ext)
%     (of(tau A_inferred (TradAA) (TradAa) )
%        (TradAA)
%        int
%     ) :-
%     (trad AA TradAA),
%     (trad Aa TradAa),
%     of (TradAa) A_inferred int.


% [NOTAZIONI]
%   X Xx indicano tipo ed elemento
%   of elemento tipo IE
%   isType tipo Kind IE
%

