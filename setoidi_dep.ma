(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "basics/logic.ma".

record Sig (A:Type[0]) (f:A→Type[0]) : Type[0] ≝ {
    pi1: A
  ; pi2: f pi1
  }.

(******************************)

record setoid (A: Type[0]) : Type[0] ≝
 { rel : A → A → Prop
 ; refl : ∀x. rel x x
 ; sym : ∀x,y. rel x y → rel y x
 ; trans : ∀x,y,z. rel x y → rel y z → rel x z
 }.

record setoidDep (A: Type[0]) (B: A → Type[0]) (S: setoid A): Type[0] ≝
 { carrier : ∀x: A. setoid (B x)
 ; cast : ∀x,x':A. rel A S x x' → B x → B x'
 ; cast_proof: ∀x,x'. ∀p: rel … x x'. ∀y,y'.
    rel … (carrier x) y y' → rel … (carrier x') (cast … p y) (cast … p y')
 ; cast_refl : ∀x,y. rel ? (carrier x) (cast x x (refl ?? x) y) y
 ; cast_sym : ∀x,y,p,z,v. rel … (carrier x) z (cast y x p v) → 
    rel … (carrier y) (cast x y (sym … p) z) v
 ; cast_trans : ∀x1,x2,x3,p12,p23,y.
    rel ? (carrier x3) (cast x1 x3 (trans … p12 p23) y)
     (cast x2 x3 p23 (cast x1 x2 p12 y))
 }.

definition setoidSigma:
 ∀A,B.
  ∀aS: setoid A. setoidDep A B aS → setoid (Sig A B)
≝
 λA,B. λaS. λbS.
  mk_setoid ?
   (λx,x'.
    ∃p: rel ? aS (pi1 ?? x) (pi1 ?? x').
    rel ? (carrier ?? aS bS (pi1 ?? x'))
     (cast ?? aS bS ?? p (pi2 ?? x)) (pi2 ?? x'))
   ???.
 [ #x % [ @refl | @cast_refl ]
 | #x #y * #p #H % [ @(sym … p) | @cast_sym @sym @H ]
 | #x #y #z * #p1xy #p2xy * #p1yz #p2yz %
   [ @(trans … p1xy p1yz)
   | @trans [2: @cast_trans | skip ]
     @trans [2: @(cast_proof … p2xy) | skip ]
     @p2yz ]]
qed.

axiom daemon: False.

definition setoidDepGamma:
 ∀A,B,C.
  ∀sA: setoid A.
   ∀sB: setoidDep A B sA.
    setoidDep (Sig A B) C (setoidSigma ?? sA sB) →
     ∀x. (setoidDep (B x) (λy:B x.C (mk_Sig A B x y)) (carrier A B sA sB x)).
#A #B #C #sA #sB #sAB #x %
 [ #y @(carrier ??? sAB)
 | #y #y' #p @(cast ??? sAB)
   % [ @refl | @trans [2: @cast_refl | skip] @p ]
 | #y #y' #px @cast_proof
 | #y #z @cast_refl
 | #y1 #y2 #p @cast_sym 
 | #y1 #y2 #y3 #p12 #p23 #y @cast_trans
 ]
qed.

definition setoidDepSigma:
 ∀A,B,C.
  ∀sA: setoid A.
   ∀sB: setoidDep A B sA.
    setoidDep (Sig A B) C (setoidSigma ?? sA sB) →
     setoidDep A (λx. Sig (B x) (λy. C (mk_Sig ?? x y))) sA
≝ ?.
#A #B #C #sA #sB #sAB %
 [ #x @setoidSigma
   [ @(carrier ??? sB)
   | @(setoidDepGamma … sAB) ]
 | #x #x' #p * #y #z %
    [ @(cast … sB … p y)
    | @(cast … sAB … z) % [ @p | @refl ]]
 | #x #x' #p #y #y' #py cases daemon
 | #x * #y #z normalize % [ @cast_refl | cases daemon ]
 | #x1 #x2 #p * #y1 #z1 * #y2 #z2 * #H #K %
   [ @cast_sym @H
   | cases daemon ]
 | #x1 #x2 #x3 #p12 #p23 * #y1 #z1 %
   [ @cast_trans
   | cases daemon ]]
qed.

definition setoidPi:
 ∀A,B.
  ∀aS: setoid A. setoidDep A B aS → setoid (∀x: A. B x)
≝
 λA,B. λaS. λbS.
  mk_setoid ?
   (λf,f'. ∀x. rel ? (carrier ?? aS bS x)(f x) (f' x))
   ???.
 [ #f #x @refl
 | #f1 #f2 #p #x @sym @p
 | #f1 #f2 #f3 #p12 #p23 #x @(trans … (p12 x) (p23 x)) ]
qed.

definition setoidDepPi:
 ∀A,B,C.
  ∀sA: setoid A.
   ∀sB: setoidDep A B sA.
    setoidDep (Sig A B) C (setoidSigma ?? sA sB) →
     setoidDep A (λx. ∀y: B x. C (mk_Sig ?? x y)) sA
≝ ?.
#A #B #C #sA #sB #sAB %
 [ #x @setoidPi
   [ @(carrier ??? sB)
   | @(setoidDepGamma … sAB) ]
 | #x #x' #p #f #y @(cast … (setoidSigma … sA sB) sAB … (f ?))
   [2: @(cast … sB … (sym … p) y)
   | %{p} @cast_sym [ @sym @p | @refl ]]
 | #x #x' #p #f #f' #pf #y whd in pf; cases daemon
 | #x #f #y cases daemon
 | #x #x' #p #f #f' #pf #y cases daemon
 | cases daemon ]
qed.

inductive singleton : Type[0] ≝ star : singleton.

definition setoidSingleton : setoid singleton ≝
 mk_setoid ? (λx,y. x = y) ???.
 [ #x %
 | #x #y #H >H %
 | #x #y #z #H >H #K @K ]
qed.

definition setoidDepSingleton :
 ∀A. ∀sA: setoid A. setoidDep A (λx. singleton) sA.
 #A #sA %
  [ #x @setoidSingleton
  | #x #x' #p @(λy.y)
  | #x #x' #p #y #y' #q @q
  | #x #y @refl
  | #x #y #p #z #w #q @q
  | #x1 #x2 #x3 #p12 #p23 #y % ]
qed.

axiom P: singleton → Type[0].
axiom Q: ∀x:singleton. P x → Type[0].

definition Q' ≝ λp: Sig singleton P. Q (pi1 … p) (pi2 … p).

(* ∀x: singleton. Σy: P x. Q x y *)
definition test ≝
 setoidPi singleton (λx. Sig ? (λy: P x. Q' (mk_Sig … x y))) ??.
 [ @setoidSingleton
 | @setoidDepSigma
   [ cases daemon (* setoidDep singleton P ? *)
   | cases daemon (* setoidDep (Sig singleton P) Q' ? *) ]]
qed.