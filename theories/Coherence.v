From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Export seq.
From Domains Require Import Preamble Preorder Poset Dcpo.
From Coq Require Import Relations.

Unset Program Cases.
Local Obligation Tactic := auto.
Set Bullet Behavior "None".

(** * Coherence spaces *)

(** ** Definition *)

Record space :=
  {
    token : Type;          (* can be made a countType (Ehrhard, Jafar-Rahmani, 2019) *)
    coh: relation token;
    coh_refl: reflexive _ coh;
    coh_symm: symmetric _ coh;
  }.

Arguments coh {_}.
Bind Scope coh_scope with space.
Delimit Scope coh_scope with coh.

(** ** Cliques *)

(** A point in a coherence space is a set of pairwise coherent tokens. *)

Record clique (A : space) :=
  {
    has : token A -> Prop;
    has_coh a b : has a -> has b -> coh a b;
  }.

Arguments has {A}.
Bind Scope clique_scope with clique.
Delimit Scope clique_scope with clique.
Open Scope clique_scope.

(** ** Ordering *)

(* Points are ordered by inclusion and form a DCPPO. *)

Definition ref {A} : relation (clique A) :=
  fun x y => forall a, has x a -> has y a.

Lemma refR {A} : reflexive _ (@ref A).
Proof. by move=>c ta. Qed.

Lemma refT {A} : transitive _ (@ref A).
Proof.
move=>cx cy cz Hxy Hyz ta Ha.
by apply/Hyz/Hxy.
Qed.

HB.instance Definition ref_preo A := PreorderOfType.Build (clique A) ref refR refT.

Lemma refA {A} : antisymmetric _ (@ref A).
Proof.
move=>[ha ca][hb cb]; rewrite /ref /= => Hxy Hyx.
have E: ha = hb.
- by apply: funext=>t; apply: propext; split; [apply: Hxy | apply: Hyx].
rewrite E in ca cb *.
by rewrite (proofirr _ ca cb).
Qed.

HB.instance Definition ref_po A := PosetOfPreorder.Build (clique A) refA.

(** ** DCPPO structure *)

(** *** Least element *)

Program Definition bot A : clique A :=
  {|
    has a := False;
  |}.
Next Obligation. by []. Qed.

Lemma ref_bot {A} : ∃ x : clique A, is_bottom x.
Proof. by exists (bot A)=>x a. Qed.

HB.instance Definition ref_ppo A := PointedPosetOfPoset.Build (clique A) ref_bot.

(** *** Directed supremum *)

Program Definition lim {A} (F : Family (clique A)) (D : is_directed F) : clique A :=
  {|
    has a := exists i, has (fam_val F i) a;
  |}.
Next Obligation.
move=>A F [_ P] i j [x Hx][y Hy].
case: (P x y)=>z [Fx Fy].
move: (Fx i Hx)=>Hz1; move: (Fy j Hy)=>Hz2.
by apply: (has_coh _ (F z) _ _ Hz1 Hz2).
Qed.

Lemma ref_HasDLubs {A} (F : Family (clique A)) : is_directed F → ∃ x, is_lub F x.
Proof.
move=>/= D; exists (lim _ D); split=>/=.
- by move=>q ta Ha /=; exists q.
by move=>c Hc a /= [q Hq]; apply: (Hc q).
Qed.

HB.instance Definition ref_dcpo A := DcpoOfPoset.Build (clique A) ref_HasDLubs.

(** * Basic categorical structure *)

(** ** Linear maps *)

(** *** Definition *)

(** Linear maps are defined as cliques in the space [A --o B]. *)

Program Definition lmap (A B : space) : space :=
  {|
    token := token A * token B;
    coh '(a1, b1) '(a2, b2) :=
      coh a1 a2 -> coh b1 b2 /\ (b1 = b2 -> a1 = a2);
  |}.
Next Obligation.
move=>A B [a b] _; split=>//.
by apply: coh_refl.
Qed.
Next Obligation.
move=>A B [a1 b1][a2 b2] H /coh_symm /H; case=>Hb He.
split; first by apply: coh_symm.
by move=>E; symmetry; apply: He.
Qed.

Infix "--o" := lmap (at level 55, right associativity) : coh_scope.
Notation "A --o B" := (clique (A --o B)) : type_scope.

(** *** Properties *)

Lemma lmap_cohdet {A B} (f : A --o B) (a1 a2 : token A) (b1 b2 : token B) :
  coh a1 a2 -> has f (a1, b1) -> has f (a2, b2) ->
  coh b1 b2 /\ (b1 = b2 -> a1 = a2).
Proof. by move=>Ha H1 H2; case: (has_coh _ f _ _ H1 H2 Ha). Qed.

Lemma lmap_ext {A B} (f g : A --o B):
  (forall x y, has f (x, y) <-> has g (x, y)) -> f = g.
Proof. by move=>H; apply: ltE; case=>a b Ha; apply/H. Qed.

(** ** Identity and composition *)

Program Definition lmap_id {A : space} : A --o A :=
  {|
    has '(x, y) := x = y;
  |}.
Next Obligation. by move=>A [a1 b1] [a2 b2] /= ->->. Qed.

Program Definition lmap_compose {A B C} (g : B --o C) (f : A --o B) : A --o C :=
  {|
    has '(x, z) := exists y, has f (x, y) /\ has g (y, z);
  |}.
Next Obligation.
move=>A B C [tg cg] [tf cf] [a1 c1] [a2 c2] /= [x [Hx1 Hx2]][y [Hy1 Hy2]] H.
move: (cf _ _ Hx1 Hy1)=>/(_ H); case=>Hxy Exy.
move: (cg _ _ Hx2 Hy2)=>/(_ Hxy); case=>Hc Ec.
by split=>// /Ec/Exy.
Qed.

Infix "@" := lmap_compose (at level 30, right associativity) : clique_scope.

Lemma lmap_compose_id_left {A B} (f : A --o B) :
  f @ lmap_id = f.
Proof.
apply: lmap_ext=>x y /=; split.
- by case=>z [->].
by move=>H; exists x.
Qed.

Lemma lmap_compose_id_right {A B} (f : A --o B) :
   lmap_id @ f = f.
Proof.
apply: lmap_ext=>x y /=; split.
- by case=>z [+ <-].
by move=>H; exists y.
Qed.

Lemma lmap_compose_assoc {A B C D} (h : C --o D) (g : B --o C) (f : A --o B) :
  (h @ g) @ f = h @ (g @ f).
Proof.
apply: lmap_ext=>x y /=; split.
- by case=>z [Hz][w][Hzw Hwy]; exists w; split=>//; exists z.
by case=>z [[w][Hxw Hwx]] H; exists w; split=>//; exists z.
Qed.

(** ** Action on cliques *)

(** The [clique A] type defines a functor of type [Coh -> Set]. Its
  action on linear maps transports them to functions on cliques. *)

Program Definition lmap_apply {A B} (f : A --o B) (x : clique A) : clique B :=
  {|
    has b := exists a, has x a /\ has f (a, b);
  |}.
Next Obligation.
move=>A B [tf cf] [tx cx] a b [y][/= Hxy Hfy][z][Hxz Hfz].
move: (cx _ _ Hxy Hxz)=>Hc.
by move: (cf _ _ Hfy Hfz)=>/(_ Hc) [].
Qed.

Lemma lmap_apply_id {A} (x : clique A) :
  lmap_apply lmap_id x = x.
Proof.
apply: ltE.
- by move=>a [b][H <-].
by move=>a Ha /=; exists a.
Qed.

Lemma lmap_apply_compose {A B C} (f : A --o B) (g : B --o C) (x : clique A) :
  lmap_apply (g @ f) x = lmap_apply g (lmap_apply f x).
Proof.
apply: ltE.
- by move=>c /= [a][Ha][b][Hfb Hgb]; exists b; split=>//; exists a.
by move=>c /= [b][[a][Ha Hf] Hb]; exists a; split=>//; exists b.
Qed.

(* Equivalence *)

Definition lequiv (A B : space) : Type :=
  (A --o B) * (B --o A).

Infix "o--o" := lequiv (at level 60, right associativity) : coh_scope.

(** ** Linear isomorphisms *)
(*
Record liso (A B : space) :=
  {
    liso_of :> token A -> token B -> Prop;
    liso_coh a1 a2 b1 b2 :
      liso_of a1 b1 ->
      liso_of a2 b2 ->
      (coh a1 a2 <-> coh b1 b2) /\
      (a1 = a2 <-> b1 = b2)
  }.

Arguments liso_of {A B}.
Infix "=~=" := liso (at level 70, right associativity) : type_scope.

Program Definition li_fw {A B} (f : A =~= B) : A --o B :=
  {|
    has '(a, b) := liso_of f a b;
  |}.
Next Obligation.
move=>A B [l H] [a1 b1][a2 b2] /= L1 L2 Ca.
by case: (H _ _ _ _ L1 L2)=>Hc He; split; [apply/Hc | move/He].
Qed.

Program Definition li_bw {A B} (f : A =~= B) : B --o A :=
  {|
    has '(a, b) := liso_of f b a;
  |}.
Next Obligation.
move=>A B [l H] [a1 b1][a2 b2] /= L1 L2 Ca.
by case: (H _ _ _ _ L1 L2)=>Hc He; split; [apply/Hc | move/He].
Qed.

Lemma li_bw_fw {A B} (f : A =~= B) :
  li_fw f @ li_bw f = lmap_id.
Proof.
apply: lmap_ext=>x y; case: f=>l H /=; split.
- case=>z [L1 L2].
  by case: (H _ _ _ _ L1 L2)=>_ He; apply/He.
move=>->. exists y.
  destruct f as [f Hf]; cbn in *.
  split.
  - intros (b & Hxb & Hby). cbn in *.
    destruct (Hf b b x y); auto. firstorder.
  - intros [ ]. exists x.
 apply liso_coh.
*)


(** * Simple constructions *)

(** ** Output *)

(** The covariant functor from [Set]. In terms of cliques this is the
  flat domain generated by [X]. *)

Program Definition output (X : Type) : space :=
  {|
    token := X;
    coh := eq;
  |}.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.

Program Definition omap {X Y} (f : X -> Y) : output X --o output Y :=
  {|
    has '(x, y) := f x = y;
  |}.
Next Obligation.
by move=>X Y f [a1 b1] [a2 b2] /= <-<- ->.
Qed.

Lemma omap_id {X} :
  omap (fun x:X => x) = lmap_id.
Proof. by apply: lmap_ext=>x y. Qed.

Lemma omap_compose {X Y Z} (f : X -> Y) (g : Y -> Z) :
  omap (fun x:X => g (f x)) = omap g @ omap f.
Proof.
apply: lmap_ext=>/= x y; split.
- by move=><-; exists (f x).
by case=>z[->].
Qed.

(** In fact, [output] is the left adjoint to [clique]. Here we give a
  characterization in terms of universal morphisms. *)

Program Definition oret {A} (a : A) : clique (output A) :=
  {|
    has := eq a;
  |}.
Next Obligation. by move=>A a x b=>->. Qed.

Program Definition oext {A B} (f : A -> clique B) : output A --o B :=
  {|
    has '(a, b) := has (f a) b;
  |}.
Next Obligation.
move=>A B f [a1 b1] [a2 b2] /= Ha Hb E; split=>//.
by apply: (has_coh _ _ _ _ Ha); rewrite E.
Qed.

Lemma oext_oret {A B} (f : A -> clique B) (a : A) :
  lmap_apply (oext f) (oret a) = f a.
Proof.
apply: ltE.
- by move=>b /= [x][->].
by move=>b /= H; exists a.
Qed.

Lemma oext_uniq {A B} (f : A -> clique B) (g : output A --o B) :
  (forall a, lmap_apply g (oret a) = f a) ->
  g = oext f.
Proof.
move=>H; apply: lmap_ext=>x y /=.
rewrite -H /=; split.
- by move=>Hg; exists x.
by case=>a [->].
Qed.

(** Here we could prove some consequences, in particular the
  isomorphisms between [output (A + B)] and [output A + output B],
  and between [clique (A && B)] and [clique A * clique B]. *)

(** ** Input *)

(** A contravariant functor from [Set]. Here the domain we obtain is
  essentially the powerset of [X]. For what its worth I believe the
  adjoint is the "coclique" contravariant functor [clique @ lneg]. *)

Program Definition input (X : Type) : space :=
  {|
    token := X;
    coh x1 x2 := True;
  |}.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.

Program Definition imap {X Y} (f : X -> Y) : input Y --o input X :=
  {|
    has '(y, x) := f x = y;
  |}.
Next Obligation.
by move=>X Y f [a1 b1] [a2 b2] /= <- <- _; split=>// ->.
Qed.

Lemma imap_id {X} :
  imap (fun x:X => x) = lmap_id.
Proof. by apply: lmap_ext=>x y. Qed.

Lemma imap_compose {X Y Z} (f : X -> Y) (g : Y -> Z) :
  imap (fun x:X => g (f x)) = imap f @ imap g.
Proof.
apply: lmap_ext=>/= z x; split.
- by move=><-; exists (f x).
by case=>y [<- ->].
Qed.

(* Partial functions *)

Program Definition pmap (A B : space) : space :=
  {|
    token := token A * token B;
    coh '(a1, b1) '(a2, b2) := a1 = a2 -> b1 = b2;
  |}.
Next Obligation. by move=>A B [a1 b1]. Qed.
Next Obligation.
by move=>A B [a1 b1][a2 b2] H E; rewrite H.
Qed.

(** * Cartesian structure *)

(** ** Binary product *)

(** *** Definition *)

Variant csprod_coh {A B} (RA : relation A) (RB : relation B) : relation (A + B) :=
  | inl_coh x y : RA x y -> csprod_coh RA RB (inl x) (inl y)
  | inr_coh x y : RB x y -> csprod_coh RA RB (inr x) (inr y)
  | inl_inr_coh x y : csprod_coh RA RB (inl x) (inr y)
  | inr_inl_coh x y : csprod_coh RA RB (inr x) (inl y).

Program Definition csprod (A B : space) : space :=
  {|
    token := token A + token B;
    coh := csprod_coh coh coh;
  |}.
Next Obligation.
move=>A B; case.
- move=>a; apply: inl_coh.
  by apply: coh_refl.
move=>b; apply: inr_coh.
by apply: coh_refl.
Qed.
Next Obligation.
move=>A B x y H; case: {-1}_ {-1}_ / H (erefl x) (erefl y) => a b.
- by move=>H _ _; apply/inl_coh/coh_symm.
- by move=>H _ _; apply/inr_coh/coh_symm.
- by move=>_ _; apply: inr_inl_coh.
by move=>_ _; apply: inl_inr_coh.
Qed.

Infix "&&" := csprod : coh_scope.

Program Definition csp1 {A B : space} : A && B --o A :=
  {|
    has '(x, a) := inl a = x;
  |}.
Next Obligation.
move=>A B [a1 b1][a2 b2] /= <-<- H.
case: {-1}_ {-1}_ / H (erefl (@inl _ (token B) b1)) (erefl (@inl _ (token B) b2))=>//.
by move=>x y H; case=>->; case=>->; split=>//->.
Qed.

Program Definition csp2 {A B : space} : A && B --o B :=
  {|
    has '(x, b) := inr b = x;
  |}.
Next Obligation.
move=>A B [a1 b1][a2 b2] /= <-<- H.
case: {-1}_ {-1}_ / H (erefl (@inr (token A) _ b1)) (erefl (@inr (token A) _ b2))=>//.
by move=>x y H; case=>->; case=>->; split=>//->.
Qed.

Program Definition cspair {X A B: space} (f: X --o A) (g: X --o B): X --o A && B :=
  {|
    has '(x, y) :=
      match y with
        | inl a => has f (x, a)
        | inr b => has g (x, b)
      end;
  |}.
Next Obligation.
move=>X A B f g /= [a1 b1][a2 b2]; case: b2=>b2; case: b1=>b1 H1 H2 Hc.
- case: (lmap_cohdet _ _ _ _ _ Hc H1 H2)=>Hcb E.
  by split; [apply: inl_coh | case].
- by split=>//; apply: inr_inl_coh.
- by split=>//; apply: inl_inr_coh.
case: (lmap_cohdet _ _ _ _ _ Hc H1 H2)=>Hcb E.
by split; [apply: inr_coh | case].
Qed.

Notation "{ x , y }" := (cspair x y) (x at level 99) : clique_scope.

(** *** Universal property *)

Lemma cspair_csp1 {X A B} (f : X --o A) (g : X --o B) :
  csp1 @ {f, g} = f.
Proof.
apply: lmap_ext=>x a /=; split.
- by case; case=>z; case=>// + [->].
by move=>Hxa; exists (inl a).
Qed.

Lemma cspair_csp2 {X A B} (f : X --o A) (g : X --o B) :
  csp2 @ {f, g} = g.
Proof.
apply: lmap_ext=>x b /=; split.
- by case; case=>z; case=>// + [->].
by move=>Hxb; exists (inr b).
Qed.

Lemma cspair_uniq {X A B} (h : X --o A && B) :
  {csp1 @ h, csp2 @ h} = h.
Proof.
apply: lmap_ext=>x; case=>/=.
- move=>a; split.
  - by case; case=>z; case=>// + [->].
  by move=>Hxa; exists (inl a).
move=>b; split.
- by case; case=>z; case=>// + [->].
by move=>Hxb; exists (inr b).
Qed.

(** ** Binary coproducts *)

(** *** Definition *)

Inductive cssum_coh {A B} (RA: relation A) (RB: relation B): relation (A + B) :=
  | sum_inl_coh x y : RA x y -> cssum_coh RA RB (inl x) (inl y)
  | sum_inr_coh x y : RB x y -> cssum_coh RA RB (inr x) (inr y).

Program Definition cssum (A B : space) : space :=
  {|
    token := token A + token B;
    coh := cssum_coh coh coh;
  |}.
Next Obligation.
move=>A B; case=>x.
- by apply/sum_inl_coh/coh_refl.
by apply/sum_inr_coh/coh_refl.
Qed.
Next Obligation.
move=>A B x y H; case: {-1}_ {-1}_ / H (erefl x) (erefl y) => a b.
- by move=>H _ _; apply/sum_inl_coh/coh_symm.
by move=>H _ _; apply/sum_inr_coh/coh_symm.
Qed.

Infix "+" := cssum : coh_scope.

Program Definition csi1 {A B : space} : A --o A + B :=
  {|
    has '(a, x) := inl a = x;
  |}.
Next Obligation.
move=>A B [a1 _][a2 _]<-<- Ha; split=>/=; last by case.
by apply: sum_inl_coh.
Qed.

Program Definition csi2 {A B : space} : B --o A + B :=
  {|
    has '(b, x) := inr b = x;
  |}.
Next Obligation.
move=>A B [a1 _][a2 _]<-<- Ha; split=>/=; last by case.
by apply: sum_inr_coh.
Qed.

Program Definition copair {A B X: space} (f: A --o X) (g: B --o X) : A+B --o X :=
  {|
    has '(x, y) :=
      match x with
        | inl a => has f (a, y)
        | inr b => has g (b, y)
      end;
  |}.
Next Obligation.
move=>A B X f g [ab1 x1][ab2 x2] /= H1 H2 H.
case: {-1}_ {-1}_ / H (erefl ab1) (erefl ab2) => a b H E1 E2;
rewrite {ab1}E1 in H1; rewrite {ab2}E2 in H2;
by case: (lmap_cohdet _ _ _ _ _ H H1 H2)=>Hx E; split=>// /E ->.
Qed.

Notation "[ x , y ]" := (copair x y) (x at level 99) : clique_scope.

(** *** Universal property *)

Lemma copair_csi1 {A B X} (f : A --o X) (g : B --o X) :
  [f, g] @ csi1 = f.
Proof.
apply: lmap_ext=>a x /=; split.
- by case; case=>z; case=>//; case=>->.
by move=>Hax; exists (inl a).
Qed.

Lemma copair_csi2 {A B X} (f : A --o X) (g : B --o X) :
  [f, g] @ csi2 = g.
Proof.
apply: lmap_ext=>b x /=; split.
- by case; case=>z; case=>//; case=>->.
by move=>Hax; exists (inr b).
Qed.

Lemma copair_uniq {A B X} (h : A + B --o X) :
  [h @ csi1, h @ csi2] = h.
Proof.
apply: lmap_ext; case=>[a|b] x /=; split.
- by case; case=>z; case=>//; case=>->.
- by move=>Hax; exists (inl a).
- by case; case=>z; case=>//; case=>->.
by move=>Hax; exists (inr b).
Qed.

(** ** Terminal object *)

(** *** Definition *)

Program Definition csterm : space :=
  {|
    token := Empty_set;
    coh x y := True;
  |}.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.

(** *** Universal property *)

Program Definition discard A : A --o csterm :=
  {|
    has '(x, y) := False;
  |}.
Next Obligation. by move=>A [a1 b1][a2 b2]. Qed.

Lemma discard_uniq {A} (f : A --o csterm) :
  f = discard A.
Proof. by apply: lmap_ext=>x. Qed.


(** * Tensor product *)

(** ** Definition *)

Program Definition cstens (A B : space) : space :=
  {|
    token := token A * token B;
    coh '(a1, b1) '(a2, b2) := coh a1 a2 /\ coh b1 b2;
  |}.
Next Obligation.
by move=>A B [a b]; split; apply: coh_refl.
Qed.
Next Obligation.
by move=>A B [a1 b1] [a2 b2] [Ha Hb]; split; apply: coh_symm.
Qed.

Infix "*" := cstens : coh_scope.

(** ** Functoriality *)

Program Definition cstens_lmap {A B C D} (f : A --o B) (g : C --o D) : A*C --o B*D :=
  {|
    has '((a, c), (b, d)) := has f (a, b) /\ has g (c, d);
  |}.
Next Obligation.
move=>A B C D f g [[a1 c1][b1 d1]][[a2 c2][b2 d2]][Hab1 Hcd1][Hab2 Hcd2][Ha Hc] /=.
case: (lmap_cohdet _ _ _ _ _ Ha Hab1 Hab2)=>Hb1 E1.
case: (lmap_cohdet _ _ _ _ _ Hc Hcd1 Hcd2)=>Hd1 E2.
by do !split=>//; case=>/E1 -> /E2 ->.
Qed.

Infix "*" := cstens_lmap : clique_scope.

Lemma cstens_id {A B} :
  (@lmap_id A) * (@lmap_id B) = lmap_id.
Proof.
by apply: lmap_ext=>[[a1 b1] [a2 b2]] /=; split; case=>->->.
Qed.

Lemma cstens_compose {A1 B1 C1} {A2 B2 C2}
    (f1 : A1 --o B1) (g1 : B1 --o C1) (f2 : A2 --o B2) (g2 : B2 --o C2) :
    (g1 @ f1) * (g2 @ f2) = (g1 * g2) @ (f1 * f2).
Proof.
apply: lmap_ext=>[[a1 a2][c1 c2]] /=; split.
- by case=>[[b1][Hf1 Hg1]][b2][Hf2 Hg2]; exists (b1, b2).
by case=>[[b1 b2][[Hf1 Hf2][Hg1 Hg2]]]; split; [exists b1 | exists b2].
Qed.

(** ** Unit *)

Program Definition csunit : space :=
  {|
    token := unit;
    coh x y := True;
  |}.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.

Notation "1" := csunit : coh_scope.

(** Left unitor *)

Program Definition lam A : 1 * A --o A :=
  {|
     has '((_, a), b) := a = b;
  |}.
Next Obligation.
by move=>A [[[] a1] b1][[[] a2] b2] /= ->-> [_ H]; split=>// ->.
Qed.

(** Right unitor *)

Program Definition rho A : A * 1 --o A :=
  {|
  has '((a, _), b) := a = b;
  |}.
Next Obligation.
by move=>A [[a1 []] b1][[a2 []] b2] /= ->-> [H _]; split=>// ->.
Qed.

(* etc.. *)

(** ** Negation *)

(** To avoid confusion between the [coh] relation associated with [A]
  and [lneg A], we introduce this singleton type. *)

Variant lneg_token A :=
  | ln (a : token A).

Arguments ln {A}.

Definition incoh A : relation (token A) :=
  fun x y => coh x y -> x = y.

Arguments incoh {_}.

Variant lneg_coh (A : space) : relation (lneg_token A) :=
  lneg_coh_intro x y :
    incoh x y -> lneg_coh A (ln x) (ln y).

Program Definition lneg (A : space) : space :=
  {|
    token := lneg_token A;
    coh := lneg_coh A;
  |}.
Next Obligation.
by move=>A [a]; apply: lneg_coh_intro.
Qed.
Next Obligation.
by move=>A _ _ [x y H]; apply: lneg_coh_intro=>/coh_symm/H.
Qed.

Program Definition lmap_flip {A B} (f : A --o B) : lneg B --o lneg A :=
  {|
    has '((ln x), (ln y)) := has f (y, x);
  |}.
Next Obligation.
move=>A B f [[b1 [a1]] [[b2][a2]]] H1 H2 /= H.
case: {-1}_ {-1}_ / H (erefl (ln b1) ) (erefl (ln b2))=>a b E [E1][E2].
rewrite {b1}E1 in H1; rewrite {b2}E2 in H2; split.
- apply: lneg_coh_intro=>H.
  by case: (lmap_cohdet _ _ _ _ _ H H1 H2)=>Hb1; apply; apply: E.
case=>Ea; rewrite {a1}Ea in H1.
have H := coh_refl _ a2.
by case: (lmap_cohdet _ _ _ _ _ H H1 H2)=>/E->.
Qed.

Program Definition neg_inv_t {A} : A --o lneg (lneg A) :=
  {|
    has '(a, ln (ln b)) := a = b;
  |}.
Next Obligation.
move=>A [a1 [[b1]]][a2 [[b2]]] {a1}->{a2}->/= H; split; last by case.
apply: lneg_coh_intro=>/= H2.
case: {-1}_ {-1}_ / H2 (erefl (ln b1)) (erefl (ln b2)) H.
by move=>x y E [->][->] /E ->.
Qed.

(*

Program Definition neg_clique {A} (cl : clique A) : clique (lneg A) :=
{|
  has '(ln a) := ~ has cl a;
|}.
Next Obligation.
move=>A [h Hc][a][b] /= Ha Hb.
apply: lneg_coh_intro=>H.

*)


(*
Program Definition neg_inv_f {A} : lneg (lneg A) --o A :=
  {|
    has '(ln (ln a), b) := a = b;
  |}.
Next Obligation.
move=>A [[[a1]] b1][[[a2]] b2] /=.
move=>E1 E2 H.
case: {-1}_ {-1}_ / H (erefl (@ln (lneg _) (ln a1))) (erefl (@ln (lneg _) (ln a2))).
move=>[x][y]; rewrite /incoh /= => H [Ex][Ey].
rewrite {a1}Ex in E1; rewrite {a2}Ey in E2.
*)

(** * Sequential constructions *)

(** ** Composition *)

Program Definition sequ (A B : space) : space :=
  {|
    token := token A * token B;
    coh '(a1, b1) '(a2, b2) := coh a1 a2 /\ (a1 = a2 -> coh b1 b2);
  |}.
Next Obligation.
by move=>A B [a b]; split=>[|_]; apply: coh_refl.
Qed.
Next Obligation.
move=>A B [a1 b1][a2 b2][Ha Hb]; split; first by apply: coh_symm.
by move=>E; rewrite E in Hb; apply/coh_symm/Hb.
Qed.

Infix ";;" := sequ (at level 40, left associativity) : coh_scope.

Program Definition sequ_lmap {A B C D} (f : A --o B) (g : C --o D) :
    (A ;; C) --o (B ;; D) :=
  {|
    has '((a, c), (b, d)) := has f (a, b) /\ has g (c, d);
  |}.
Next Obligation.
move=>A B C D f g [[a1 c1][b1 d1]][[a2 c2][b2 d2]] /=
  [Hab1 Hcd1] [Hab2 Hcd2] [Ha Ea].
case: (lmap_cohdet _ _ _ _ _ Ha Hab1 Hab2)=>Hb Eb; split.
- split=>// /Eb/Ea Hc.
  by case: (lmap_cohdet _ _ _ _ _ Hc Hcd1 Hcd2).
case=>/Eb /[dup] /Ea Hc ->.
by case: (lmap_cohdet _ _ _ _ _ Hc Hcd1 Hcd2)=>Hd /[apply] ->.
Qed.

Infix ";;" := sequ_lmap : lmap_scope.

(** ** Exponential *)

(* finite clique *)
(* shouldn't this actually relate all possible pairs? *)
Inductive seq_coh (A : space) : relation (seq (token A)) :=
  | nil_coh_l s :
      seq_coh A [::] s
  | nil_coh_r s :
      seq_coh A s [::]
  | cons_coh a b x y :
      coh a b ->
      (a = b -> seq_coh A x y) ->
      seq_coh A (a :: x) (b :: y).

Lemma seq_coh_cons {A} x xs y ys :
  seq_coh A (x::xs) (y::ys) -> coh x y /\ (x = y -> seq_coh A xs ys).
Proof.
move=>H; case: {-1}_ {-1}_ / H (erefl (x :: xs)) (erefl (y :: ys))=>//.
by move=>p q ps qs H E [{x}->{xs}->][{y}->{ys}->].
Qed.

Program Definition dag (A : space) : space :=
  {|
    token := seq (token A);
    coh := seq_coh A;
  |}.
Next Obligation.
move=>A; elim=>[|x s IH]; first by apply: nil_coh_l.
by apply: cons_coh=>//; apply: coh_refl.
Qed.
Next Obligation.
move=>A s t; elim=>{s t}[s|t|x y s t H H1 H2].
- by apply: nil_coh_r.
- by apply: nil_coh_l.
apply: cons_coh; first by apply: coh_symm.
by move=>E; apply: H2.
Qed.

Notation "! A" := (dag A)
  (at level 8, right associativity, format "'!' A") : coh_scope.

(** *** Comonad structure *)

Lemma prefix_coh {A} s1 s2 t1 t2 :
  seq_coh A (s1 ++ t1) (s2 ++ t2) ->
  seq_coh A s1 s2.
Proof.
move E1: (s1 ++ t1)=>st1; move E2: (s2 ++ t2)=>st2.
move=>H; elim: H s1 s2 E1 E2.
- move=>p s1 s2. move /nilP. rewrite cat_nilp; case/andP=>/nilP-> _ _.
  by apply: nil_coh_l.
- move=>p s1 s2 _ /nilP; rewrite cat_nilp; case/andP=>/nilP-> _.
  by apply: nil_coh_r.
move=>x y p q H E IH s1 s2.
case: s1=>[|sx s1].
- by move=>_ _; apply: nil_coh_l.
case=>{sx}-> E1; case: s2=>[|sy s2].
- by move=>_; apply: nil_coh_r.
case=>{sy}-> E2; apply: cons_coh=>// Exy.
by apply: (IH Exy _ _ E1 E2).
Qed.

Lemma suffix_coh {A} s t1 t2 :
  seq_coh A (s ++ t1) (s ++ t2) ->
  seq_coh A t1 t2.
Proof.
elim: s=>//=x s IH H.
by case/seq_coh_cons: H=>_ /(_ erefl)/IH.
Qed.

Lemma app_coh {A} s t1 t2 :
  seq_coh A t1 t2 ->
  seq_coh A (s ++ t1) (s ++ t2).
Proof.
move=>Ht; elim: s=>//= x s H.
by apply: cons_coh=>//; apply: coh_refl.
Qed.

(** Action on linear maps *)

Inductive dag_lmaps {A B} (f : A --o B) : token !A -> token !B -> Prop :=
  | dag_lmaps_nil :
      dag_lmaps f [::] [::]
  | dag_lmaps_cons a b aa bb :
      has f (a, b) ->
      dag_lmaps f aa bb ->
      dag_lmaps f (a :: aa) (b :: bb).

(* TODO spec lemma? *)

Lemma dag_lmaps_lnil {A B} (f : A --o B) ys :
  dag_lmaps f [::] ys -> ys = [::].
Proof.
by move E: [::]=>e H; case: _ / H (erefl e) E.
Qed.

Lemma dag_lmaps_rnil {A B} (f : A --o B) xs :
  dag_lmaps f xs [::] -> xs = [::].
Proof.
by move E: [::]=>e H; case: _ / H (erefl e) E.
Qed.

Lemma dag_lmaps_lcons {A B} (f : A --o B) x xs zs :
  dag_lmaps f (x::xs) zs -> exists y ys, [/\ zs = y::ys,
                                             has f (x, y) &
                                             dag_lmaps f xs ys].
Proof.
move E: (x::xs)=>e H; case: _ / H (erefl e) E=>//= a y aa ys H Hs _ [Ex Exs].
rewrite -{a}Ex in H; rewrite -{aa}Exs in Hs.
by exists y, ys.
Qed.

Lemma dag_lmaps_rcons {A B} (f : A --o B) zs y ys :
  dag_lmaps f zs (y::ys) -> exists x xs, [/\ zs = x::xs,
                                             has f (x, y) &
                                             dag_lmaps f xs ys].
Proof.
move E: (y::ys)=>e H; case: _ / H (erefl e) E=>//= x b xs bb H Hs _ [Ey Eys].
rewrite -{b}Ey in H; rewrite -{bb}Eys in Hs.
by exists x, xs.
Qed.

Program Definition dag_lmap {A B} (f : A --o B) : !A --o !B :=
  {|
    has '(aa, bb) := dag_lmaps f aa bb;
  |}.
Next Obligation.
move=>A B f [aa1 bb1][aa2 bb2] Hab1 Hab2 /= Hxx.
elim: {aa1 aa2}Hxx bb1 bb2 Hab1 Hab2.
- move=>p _ bb2 /dag_lmaps_lnil -> H2; split; first by apply: nil_coh_l.
  by move=>E; rewrite -{bb2}E in H2; move/dag_lmaps_rnil: H2.
- move=>q bb1 _ H1 /dag_lmaps_lnil ->; split; first by apply: nil_coh_r.
  by move=>E; rewrite {bb1}E in H1; move/dag_lmaps_rnil: H1.
move=>a b p q Hc H IH bb1 bb2.
case/dag_lmaps_lcons=>b1[bs1][{bb1}-> H1 H11].
case/dag_lmaps_lcons=>b2[bs2][{bb2}-> H2 H22].
case: (lmap_cohdet _ _ _ _ _ Hc H1 H2)=>Cb E.
split.
- apply: cons_coh=>// /E Eab.
  by case: (IH Eab _ _ H11 H22).
case=>Eb Ebb; rewrite Eb in H1; rewrite {bs1}Ebb in H11.
move: (E Eb)=>{Cb b1 E Eb}Eab; rewrite Eab.
by case: (IH Eab _ _ H11 H22)=> _ /(_ erefl) ->.
Qed.

Notation "! f" := (dag_lmap f)
  (at level 8, right associativity, format "'!' f") : clique_scope.

Lemma dag_id {A} :
  !(@lmap_id A) = @lmap_id !A.
Proof.
apply: lmap_ext=>p q/=; split.
- by elim=>//x y {}p {}q /= -> _ ->.
by move=>->; elim: q=>[|{}x q IH]; [apply: dag_lmaps_nil | apply: dag_lmaps_cons].
Qed.

Lemma dag_compose {A B C} (f : A --o B) (g : B --o C) :
  !(g @ f) = !g @ !f.
Proof.
apply: lmap_ext=>/= xs zs; split.
- elim=>[|x z /={}xs {}zs [y][Hxy Hyz] _]; first by exists [::]; split; apply: dag_lmaps_nil.
  by case=>ys [Hxys Hyzs]; exists (y::ys); split; apply: dag_lmaps_cons.
case=>ys [H]; elim: H zs=>{xs ys}[|x y xs ys H Hs IH] zs.
- by move/dag_lmaps_lnil=>{zs}->; apply: dag_lmaps_nil.
case/dag_lmaps_lcons=>w[ws][{zs}-> Hw Hws].
by apply: dag_lmaps_cons=>/=; [exists y | apply: IH].
Qed.

(** Counit *)

Inductive dag_counit_lmaps A : token !A -> token A -> Prop :=
  dag_counit_intro a : dag_counit_lmaps A [::a] a.

(* aka dereliction *)

Program Definition dag_counit A : !A --o A :=
  {|
    has '(aa, a) := dag_counit_lmaps A aa a;
  |}.
Next Obligation.
move=>A /= [x1 _][x2 _][t1][t2] Hx; split; last by move=>->.
by case/seq_coh_cons: Hx.
Qed.

Lemma dag_counit_natural {A B} (f : A --o B) :
   f @ dag_counit A = dag_counit B @ !f.
Proof.
apply: lmap_ext=>/=xs y; split.
- case=>_ [[x] H]; exists [::y]; split.
  - by apply: dag_lmaps_cons=>//; apply: dag_lmaps_nil.
  by apply: dag_counit_intro.
case=>ys [H Hy]; case: {-1} _ / Hy (erefl y) (erefl ys) H => _ <- _.
case/dag_lmaps_rcons=>w[ws][{xs}-> H /dag_lmaps_rnil {ws}->].
by exists w.
Qed.

(** Comultiplication *)

Inductive dag_comult_lmaps {A} : token !A -> token !!A -> Prop :=
  | dag_comult_nil :
      dag_comult_lmaps [::] [::]
  | dag_comult_cons s a aa :
      dag_comult_lmaps a aa ->
      dag_comult_lmaps (s ++ a) (s :: aa).

Lemma dag_comult_rnil {A} (p : token !A) :
  dag_comult_lmaps p [::] -> p = [::].
Proof. by move E: [::]=>e H; case: {-1}_ {-1}_ / H (erefl p) (erefl e) E. Qed.

Lemma dag_comult_rcons {A} (p : token !A) s aa :
  dag_comult_lmaps p (s::aa) -> exists a, p=s++a /\ dag_comult_lmaps a aa.
Proof.
move=>H; case: {-1}_ / H (erefl p) (erefl (s::aa))=>// {p} s1 a aa1 H _ [{s1}<- {aa}->].
by exists a.
Qed.

(* aka digging *)

Program Definition dag_comult A : !A --o !!A :=
  {|
    has '(a, aa) := dag_comult_lmaps a aa;
  |}.
Next Obligation.
move=>A /= [a1 aa1][a2 aa2] H1 H2 Ha.
elim: H1 a2 aa2 Ha H2 => {a1 aa1}.
- move=>a2 aa2 Ha H2; split; first by apply: nil_coh_l.
  by case: H2.
move=>/= s1 a1 aa1 H1 IH a2 aa2 Ha H2.
elim: H2 Ha=>{a2 aa2}.
- by move=>_; split=>//; apply: nil_coh_r.
move=>s2 a2 aa2 H2 IH2 Ha; split.
- apply: cons_coh.
  - by apply: (prefix_coh _ _ _ _ Ha).
  move=>E; rewrite {s1}E in Ha IH2.
  by move/suffix_coh: Ha=>/IH/(_ H2); case.
case=>E1 E2; rewrite {s1 IH2}E1 in Ha *.
by move/suffix_coh: Ha=>/IH/(_ H2); case=>_ /(_ E2) ->.
Qed.

(* TODO move under dag_lmaps? *)
Lemma dag_lmaps_app {A B} (f : A --o B) a1 a2 b1 b2:
  has !f (a1, b1) ->
  has !f (a2, b2) ->
  has !f (a1 ++ a2, b1 ++ b2).
Proof.
move=>/=; elim=>//=a b aa bb H Hs IH /IH H2.
by apply: dag_lmaps_cons.
Qed.

Lemma dag_lmaps_app_inv {A B} (f : A --o B) a b1 b2:
  has !f (a, b1 ++ b2) ->
  exists a1 a2,
    a = a1 ++ a2 /\
    has !f (a1, b1) /\
    has !f (a2, b2).
Proof.
elim: b1 a b2=>/=[|b bs IH] a b2 H.
- by exists [::], a; do!split=>//; apply: dag_lmaps_nil.
case/dag_lmaps_rcons: H=>x[xs][{a}->H Hs].
case: (IH _ _ Hs)=>xa1[xa2][Ex [Hx1 Hx2]]; rewrite {xs}Ex in Hs *.
exists (x::xa1), xa2; do!split=>//.
by apply: dag_lmaps_cons.
Qed.

Lemma dag_comult_natural {A B} (f : A --o B) :
  !!f @ dag_comult A = dag_comult B @ !f.
Proof.
apply: lmap_ext=>/= xs yys; split.
- case=>xxs [Hxs Hxxs].
  elim: Hxs yys Hxxs=>[|s a aa H IH] yys.
  - move/dag_lmaps_lnil=>{yys}->.
    by exists [::]; split; [apply: dag_lmaps_nil | apply: dag_comult_nil].
  case/dag_lmaps_lcons=>/=ws[wws][{yys}-> Hw /IH [qs][Hq Hqs]].
  by exists (ws ++ qs); split; [apply: dag_lmaps_app | apply: dag_comult_cons].
case=>ys [Hx Hys]; elim: Hys xs Hx=>[|s b bb H IH] xs.
- move/dag_lmaps_rnil=>{xs}->.
  by exists [::]; split; [apply: dag_comult_nil | apply: dag_lmaps_nil].
case/dag_lmaps_app_inv=>xs1[xs2][{xs}->][/= Ha1 /IH [xxs][Hx Hxs]].
by exists (xs1::xxs); split; [apply: dag_comult_cons | apply: dag_lmaps_cons].
Qed.

(** Properties *)

Lemma dag_comult_counit {A} :
  !(dag_counit A) @ (dag_comult A) = @lmap_id !A.
Proof.
apply: lmap_ext=>/= xs ys; split.
- case=>xxs [Hc Hd].
  elim: Hc ys Hd=>/= [|s a aa _ IH] ys.
  - by move/dag_lmaps_lnil.
  case/dag_lmaps_lcons=>[w][ws][{ys}->/= Hcu /IH ->].
  by case: Hcu.
move=><-; exists (map (fun z=>[::z]) xs); elim: xs=>/=[|x xs [IH1 IH2]].
- by split; [apply: dag_comult_nil | apply: dag_lmaps_nil].
split; last by apply: dag_lmaps_cons.
by rewrite (_ : x::xs = [::x] ++ xs) //; apply: dag_comult_cons.
Qed.

Lemma dag_counit_comult {A} :
  (dag_counit !A) @ (dag_comult A) = @lmap_id !A.
Proof.
apply: lmap_ext=>/= xs ys; split.
- case=>xxs [Hc Hd]; case: Hd Hc=>/= {}ys.
  rewrite -(cats0 [::ys]); case/dag_comult_rcons=>x [{xs}-> /dag_comult_rnil ->].
  by rewrite cats0.
move=><-; exists [::xs]; split=>//.
by rewrite -{1}(cats0 xs); apply/dag_comult_cons/dag_comult_nil.
Qed.

Lemma dag_comult_app {A} x y xs ys:
  has (dag_comult A) (x, xs) ->
  has (dag_comult A) (y, ys) ->
  has (dag_comult A) (x ++ y, xs ++ ys).
Proof.
move=>H; elim: H y ys=>//= s a aa H IH y ys.
by move/IH=>Hd; rewrite -catA; apply: dag_comult_cons.
Qed.

Lemma dag_comult_app_inv {A} a xs ys:
  has (dag_comult A) (a, xs ++ ys) ->
  exists x y,
    a = x ++ y /\
    has (dag_comult A) (x, xs) /\
    has (dag_comult A) (y, ys).
Proof.
elim: xs a ys=>/= [|x xs IH] a ys Hys.
- by exists [::], a; do!split=>//; apply: dag_comult_nil.
case/dag_comult_rcons: Hys=>_ [{a}-> /IH [xxs][yys][->][Hxc Hyc]].
exists (x++xxs), yys; do!split=>//; first by rewrite catA.
by apply: dag_comult_cons.
Qed.

Lemma dag_comult_comult {A} :
  !(dag_comult A) @ (dag_comult A) = (dag_comult !A) @ (dag_comult A).
Proof.
apply: lmap_ext=>/= xs x3s; split.
  case=>xxs [H1 H2]; elim: H1 x3s H2=>/={xxs} [|s a aa H IH] x3s.
  - by move/dag_lmaps_lnil=>->; exists [::]; split; apply: dag_comult_nil.
  case/dag_lmaps_lcons=>/=xxs[ws][{x3s}-> Hc /IH [xxs1][Hc1 Hc2]].
  by exists (xxs ++ xxs1); split; [apply: dag_comult_app | apply: dag_comult_cons].
case=>xxs [H1 H2]; elim: H2 xs H1=>/={xxs} [|s a aa H IH] xs.
- by move/dag_comult_rnil=>->; exists [::]; split; [apply: dag_comult_nil | apply: dag_lmaps_nil].
case/dag_comult_app_inv=>ps[qs][{xs}-> /= [H1 /IH [xxs1][H2 H3]]].
by exists (ps::xxs1); split; [apply: dag_comult_cons | apply: dag_lmaps_cons].
Qed.

(** Kleisli extension *)

Definition dag_ext {A B} (f : !A --o B) : !A --o !B :=
  dag_lmap f @ dag_comult A.

Lemma dag_ext_counit A :
  dag_ext (dag_counit A) = @lmap_id !A.
Proof. by rewrite /dag_ext; apply: dag_comult_counit. Qed.

Lemma dag_counit_ext {A B} (f : !A --o B) :
  dag_counit B @ dag_ext f = f.
Proof.
by rewrite /dag_ext -lmap_compose_assoc -dag_counit_natural lmap_compose_assoc
  dag_counit_comult lmap_compose_id_left.
Qed.

Lemma dag_ext_compose {A B C} (f : !A --o B) (g : !B --o C) :
  dag_ext (g @ dag_ext f) = dag_ext g @ dag_ext f.
Proof.
by rewrite /dag_ext lmap_compose_assoc -(lmap_compose_assoc (dag_comult B))
  -dag_comult_natural !(dag_compose, lmap_compose_assoc) dag_comult_comult.
Qed.

(* par *)

Variant cspar_coh {A B} (RA : relation A) (RB : relation B) : relation (A * B) :=
  | par1_coh xa xb ya yb : RA xa xb -> xa <> xb -> cspar_coh RA RB (xa, ya) (xb, yb)
  | par2_coh xa xb ya yb : RB ya yb -> ya <> yb -> cspar_coh RA RB (xa, ya) (xb, yb)
  | parE_coh xa xb ya yb : xa = xb  -> ya = yb  -> cspar_coh RA RB (xa, ya) (xb, yb).

Program Definition cspar (A B : space) : space :=
  {|
    token := token A * token B;
    coh := cspar_coh coh coh;
  |}.
Next Obligation.
by move=>A B [a b]; apply: parE_coh.
Qed.
Next Obligation.
move=>A B [a1 b1][a2 b2]; case=>{a1 b1 a2 b2}xa xb ya yb.
- by move=>H E; apply: par1_coh; [apply/coh_symm | move=>Eq; apply: E].
- by move=>H E; apply: par2_coh; [apply/coh_symm | move=>Eq; apply: E].
by move=>->->; apply: parE_coh.
Qed.
