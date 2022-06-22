From Coq Require Import ssreflect ssrbool ssrfun.
From Domains Require Import Preamble Preorder Poset Dcpo.
From mathcomp Require Export ssrnat seq eqtype choice fintype order.

Unset Program Cases.
Local Obligation Tactic := auto.
Set Bullet Behavior "None".

(** * Coherence spaces *)

(** ** Definition *)

Import Order.POrderTheory.
Open Scope order_scope.

Variant four := Coh | Bot | Unit | Incoh.

Definition pickle4 (a : four) : nat :=
  match a with
  | Coh   => 0
  | Bot   => 1
  | Unit  => 2
  | Incoh => 3
  end.

Definition unpickle4 (a : nat) : option four :=
  match a with
  | 0 => Some Coh
  | 1 => Some Bot
  | 2 => Some Unit
  | 3 => Some Incoh
  | _ => None
  end.

Lemma pickle4K : pcancel pickle4 unpickle4.
Proof. by case. Qed.

Definition four_eqMixin := PcanEqMixin pickle4K.
Canonical four_eqType := Eval hnf in EqType _ four_eqMixin.

Definition four_choiceMixin := PcanChoiceMixin pickle4K.
Canonical four_choiceType := Eval hnf in ChoiceType _ four_choiceMixin.

Definition four_countMixin := PcanCountMixin pickle4K.
Canonical four_countType := Eval hnf in CountType _ four_countMixin.

(* fintype *)

Lemma four_enumP : Finite.axiom [:: Coh; Bot; Unit; Incoh].
Proof. by case. Qed.

Definition four_finMixin := Eval hnf in FinMixin four_enumP.
Canonical four_finType := Eval hnf in FinType four four_finMixin.
Lemma card_four : #|{: four}| = 4.
Proof. by rewrite cardT enumT unlock. Qed.

Definition lt4 (a b : four) : bool :=
  match a, b with
  | Incoh, Incoh => false
  | Incoh, _     => true
  | Bot  , Coh   => true
  | Bot  , _     => false
  | Unit , Coh   => true
  | Unit , _     => false
  | Coh  , _     => false
  end.

Definition le4 (e1 e2 : four) : bool :=
  match e1, e2 with
  | Incoh, _     => true
  | Bot  , Coh   => true
  | Bot  , Bot   => true
  | Bot  , _     => false
  | Unit , Coh   => true
  | Unit , Unit  => true
  | Unit , _     => false
  | Coh  , Coh   => true
  | Coh  , _     => false
  end.

Fact lt_def_four : forall x y, lt4 x y = (y != x) && (le4 x y).
Proof. by case; case. Qed.

Fact refl_four : reflexive le4.
Proof. by case. Qed.

Fact anti_four : antisymmetric le4.
Proof. by case; case. Qed.

Fact trans_four : transitive le4.
Proof. by case; case; case. Qed.

Definition four_porderMixin : lePOrderMixin four_eqType :=
  LePOrderMixin lt_def_four refl_four anti_four trans_four.
Canonical four_porderType := Eval hnf in POrderType tt four four_porderMixin.

Definition meet4 (a b : four) : four :=
  match a, b with
  | Incoh, _     => Incoh
  | _    , Incoh => Incoh
  | Unit , Bot   => Incoh
  | Bot  , Unit  => Incoh
  | Unit , _     => Unit
  | _    , Unit  => Unit
  | Bot , _      => Bot
  | _    , Bot   => Bot
  | Coh  , Coh   => Coh
  end.

Definition join4 (e1 e2 : four) : four :=
  match e1, e2 with
  | Coh, _       => Coh
  | _    , Coh   => Coh
  | Unit , Bot   => Coh
  | Bot  , Unit  => Coh
  | Unit , _     => Unit
  | _    , Unit  => Unit
  | Bot  , _     => Bot
  | _    , Bot   => Bot
  | Incoh, Incoh => Incoh
  end.

Lemma meet4C : commutative meet4.
Proof. by case; case. Qed.

Lemma join4C : commutative join4.
Proof. by case; case. Qed.

Lemma meet4A : associative meet4.
Proof. by case; case; case. Qed.

Lemma join4A : associative join4.
Proof. by case; case; case. Qed.

Lemma join4KI : forall y x, meet4 x (join4 x y) = x.
Proof. by case; case. Qed.

Lemma meet4KU : forall y x, join4 x (meet4 x y) = x.
Proof. by case; case. Qed.

Lemma leEmeet4 : forall x y, (x <= y) = (meet4 x y == x).
Proof. by case; case. Qed.

Definition four_latticeMixin : latticeMixin four_porderType :=
  LatticeMixin meet4C join4C meet4A join4A join4KI meet4KU leEmeet4.
Canonical four_latticeType :=
  Eval hnf in LatticeType four four_latticeMixin.

(* TODO stronger lattices *)

(* ? *)
Definition is_coh (t : four) : bool :=
  [|| (t == Coh), (t == Unit) | (t == Bot)].

Definition prod4 (a b : four) : four :=
  match a, b with
  | Bot  , Unit  => Bot
  | Unit , Bot   => Bot
  | Unit , Unit  => Unit
  | Incoh, _     => Incoh
  | _    , Incoh => Incoh
  | _    , _     => Coh
  end.

Lemma prod_eql a : prod4 a Unit = a.
Proof. by case: a. Qed.

Definition imp4 (e1 e2 : four) : four :=
  match e1, e2 with
  | Coh  , Coh   => Coh
  | Coh  , _     => Incoh
  | Bot  , Coh   => Coh
  | Bot  , Bot   => Unit
  | Bot  , _     => Incoh
  | Unit , Coh   => Coh
  | Unit , Bot   => Bot
  | Unit , Unit  => Unit
  | Unit , Incoh => Incoh
  | Incoh, _     => Coh
  end.

Lemma coh_imp_refl a : is_coh (imp4 a a).
Proof. by case: a. Qed.

Lemma coh_imp_coh a : is_coh (imp4 a Coh).
Proof. by case: a. Qed.

Lemma coh_imp_trans a b c :
  is_coh (imp4 a b) -> is_coh (imp4 b c) -> is_coh (imp4 a c).
Proof. by case: a; case: b; case: c. Qed.

Lemma coh_imp_app a b :
  is_coh (imp4 a b) -> is_coh a -> is_coh b.
Proof. by case: a; case: b. Qed.

Lemma coh_imp_prod a b c d :
  is_coh (imp4 a b) -> is_coh (imp4 c d) ->
  is_coh (imp4 (prod4 a c) (prod4 b d)).
Proof. by case: a; case: b; case: c; case: d. Qed.

Definition neg4 (a : four) : four :=
  match a with
  | Coh   => Incoh
  | Bot   => Unit
  | Unit  => Bot
  | Incoh => Coh
  end.

Lemma neg_inv a : neg4 (neg4 a) = a.
Proof. by case: a. Qed.

Lemma coh_imp_neg a b :
  is_coh (imp4 a b) -> is_coh (imp4 (neg4 b) (neg4 a)).
Proof. by case: a; case: b. Qed.

Definition par4 (e1 e2 : four) : four :=
  match e1, e2 with
  | Coh  , _     => Coh
  | Bot  , Coh   => Coh
  | Bot  , Unit  => Unit
  | Bot  , Bot   => Bot
  | Bot  , Incoh => Incoh
  | Unit , Coh   => Coh
  | Unit , Bot   => Unit
  | Unit , _     => Incoh
  | Incoh, Coh   => Coh
  | Incoh, _     => Incoh
  end.

Lemma par_neg a b : neg4 (par4 a b) = prod4 (neg4 a) (neg4 b).
Proof. by case: a; case: b. Qed.

Lemma par_eql a : par4 a Bot = a.
Proof. by case: a. Qed.

Lemma imp_par4 a b : imp4 a b = par4 (neg4 a) b.
Proof. by case: a; case: b. Qed.

(*
Definition seq3 (a b : four) : four :=
  match a, b with
  | Coh  , _     => Coh
  | Eq   , Coh   => Coh
  | Eq   , Eq    => Eq
  | _    , _     => Incoh
  end.

Lemma coh_imp_seq a b c d :
  is_coh (imp3 a b) -> is_coh (imp3 c d) ->
  is_coh (imp3 (seq3 a c) (seq3 b d)).
Proof. by case: a; case: b; case: c; case: d. Qed.
*)
Record space :=
  {
    token : Type;          (* can be made a countType (Ehrhard, Jafar-Rahmani, 2019) *)
    chf : token -> token -> four;
    chf_symm: forall a b, chf a b = chf b a;
    (*chf_ub: forall a, is_coh (chf a a);*)
  }.

Arguments chf {_}.
Bind Scope chf_scope with space.
Delimit Scope chf_scope with chf.

(** ** Cliques *)

(** A point in a coherence space is a set of pairwise coherent tokens. *)

Record clique (A : space) :=
  {
    has : token A -> Prop;
    has_coh a b : has a -> has b -> is_coh (chf a b);
  }.

Arguments has {A}.
Bind Scope clique_scope with clique.
Delimit Scope clique_scope with clique.
Open Scope clique_scope.

(** ** Ordering *)

(* Points are ordered by inclusion and form a DCPPO. *)

Definition ref {A} : clique A -> clique A -> Prop :=
  fun x y => forall a, has x a -> has y a.

Lemma refR {A} (a : clique A) : ref a a.
Proof. by move=>c ta. Qed.

Lemma refT {A} (a b c : clique A): ref a b -> ref b c -> ref a c.
Proof.
move=>Hxy Hyz ta Ha.
by apply/Hyz/Hxy.
Qed.

HB.instance Definition ref_preo A := PreorderOfType.Build (clique A) ref refR refT.

Lemma refA {A} (a b : clique A) : ref a b -> ref b a -> a = b.
Proof.
case: a=>[ha ca]; case: b=>[hb cb]; rewrite /ref /= => Hxy Hyx.
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
    chf '(a1, b1) '(a2, b2) := imp4 (chf a1 a2) (chf b1 b2);
  |}.
Next Obligation.
move=>A B [a1 b1][a2 b2].
by rewrite (chf_symm _ a2 a1) (chf_symm _ b2 b1).
Qed.
(*
Next Obligation.
move=>A B [a b]=>/=.
case/or3P: (chf_ub _ a)=>/eqP->; case/or3P: (chf_ub _ b)=>/eqP-> //.
Qed.
*)
(*
Next Obligation.
move=>A B [a1 b1][a2 b2].
case E1: (chf a1 a2)=>/=.
- have/chf_eq {}E1: chf a1 a2 != Eq by rewrite E1.
  by case E2: (chf b1 b2)=>/=; constructor; case=>A1; rewrite A1 in E1.
- move/eqP/chf_eq: E1=>->.
  case E2: (chf b1 b2)=>/=; constructor.
  - have/chf_eq {}E2: chf b1 b2 != Eq by rewrite E2.
    by case=>A2; rewrite A2 in E2.
  - by move/eqP/chf_eq: E2=>->.
  have/chf_eq {}E2: chf b1 b2 != Eq by rewrite E2.
  by case=>A2; rewrite A2 in E2.
have/chf_eq {}E1: chf a1 a2 != Eq by rewrite E1.
by case E2: (chf b1 b2)=>/=; constructor; case=>A1; rewrite A1 in E1.
Qed.
*)
Infix "--o" := lmap (at level 55, right associativity) : chf_scope.
Notation "A --o B" := (clique (A --o B)) : type_scope.

(** *** Properties *)

Lemma lmap_ext {A B} (f g : A --o B):
  (forall x y, has f (x, y) <-> has g (x, y)) -> f = g.
Proof. by move=>H; apply: ltE; case=>a b Ha; apply/H. Qed.

(** ** Identity and composition *)

Program Definition lmap_id {A : space} : A --o A :=
  {|
    has '(x, y) := x = y;
  |}.
Next Obligation.
move=>A [a1 b1][a2 b2] ->-> /=.
by exact: coh_imp_refl.
Qed.

Program Definition lmap_compose {A B C} (g : B --o C) (f : A --o B) : A --o C :=
  {|
    has '(x, z) := exists y, has f (x, y) /\ has g (y, z);
  |}.
Next Obligation.
move=>A B C [tg cg] [tf cf] [a1 c1] [a2 c2] /= [x [Hx1 Hx2]][y [Hy1 Hy2]].
move: (cg _ _ Hx2 Hy2)=>/=.
move: (cf _ _ Hx1 Hy1)=>/=.
by exact: coh_imp_trans.
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
move: (cx _ _ Hxy Hxz)=>/=.
move: (cf _ _ Hfy Hfz)=>/=.
by exact: coh_imp_app.
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
(*
(** ** Output *)

(** The covariant functor from [Set]. In terms of cliques this is the
  flat domain generated by [X]. *)

Program Definition output (X : eqType) : space :=
  {|
    token := X;
    chf x y := if x == y then Eq else Incoh;
  |}.
Next Obligation.
by move=>X a b /=; rewrite eq_sym.
Qed.
Next Obligation.
by move=>X a b; case: (@eqP _ a b)=>E; constructor.
Qed.

Program Definition omap {X Y : eqType} (f : X -> Y) : output X --o output Y :=
  {|
    has '(x, y) := f x = y;
  |}.
Next Obligation.
move=>X Y f [a1 b1] [a2 b2] /= <-<-; case: eqP=>//->.
by rewrite eq_refl.
Qed.

Lemma omap_id {X : eqType} :
  omap (fun x:X => x) = lmap_id.
Proof. by apply: lmap_ext=>x y. Qed.

Lemma omap_compose {X Y Z : eqType} (f : X -> Y) (g : Y -> Z) :
  omap (fun x:X => g (f x)) = omap g @ omap f.
Proof.
apply: lmap_ext=>/= x y; split.
- by move=><-; exists (f x).
by case=>z[->].
Qed.

(** In fact, [output] is the left adjoint to [clique]. Here we give a
  characterization in terms of universal morphisms. *)

Program Definition oret {A : eqType} (a : A) : clique (output A) :=
  {|
    has := eq a;
  |}.
Next Obligation.
by move=>A a x b=>/= <-<-; rewrite eq_refl.
Qed.

Program Definition oext {A : eqType} {B} (f : A -> clique B) : output A --o B :=
  {|
    has '(a, b) := has (f a) b;
  |}.
Next Obligation.
move=>A B f [a1 b1] [a2 b2] /= Ha Hb; case: eqP=>//= E.
rewrite E in Ha; move: (has_coh _ _ _ _ Ha Hb).
by case/orP=>/eqP->.
Qed.

Lemma oext_oret {A : eqType} {B} (f : A -> clique B) (a : A) :
  lmap_apply (oext f) (oret a) = f a.
Proof.
apply: ltE.
- by move=>b /= [x][->].
by move=>b /= H; exists a.
Qed.

Lemma oext_uniq {A : eqType} {B} (f : A -> clique B) (g : output A --o B) :
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

Program Definition input (X : eqType) : space :=
  {|
    token := X;
    chf x y := if x == y then Eq else Coh;
  |}.
Next Obligation.
by move=>X x y /=; rewrite eq_sym.
Qed.
Next Obligation.
by move=>X x y /=; case: (@eqP _ x y)=>E; constructor.
Qed.

Program Definition imap {X Y : eqType} (f : X -> Y) : input Y --o input X :=
  {|
    has '(y, x) := f x = y;
  |}.
Next Obligation.
move=>X Y f [a1 b1] [a2 b2] /= <-<-.
case: (@eqP _ b1 b2)=>/=.
- by move=>->; rewrite eq_refl.
by move=>_; case: ifP.
Qed.

Lemma imap_id {X: eqType} :
  imap (fun x:X => x) = lmap_id.
Proof. by apply: lmap_ext=>x y. Qed.

Lemma imap_compose {X Y Z : eqType} (f : X -> Y) (g : Y -> Z) :
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
    chf '(a1, b1) '(a2, b2) := if chf a1 a2 == Eq then chf b1 b2 else Incoh;
  |}.
Next Obligation.
by move=>A B [a1 b1][a2 b2]; rewrite chf_symm (chf_symm _ b1).
Qed.
Next Obligation.
move=>A B [a1 b1][a2 b2] /=; case: ifP=>/chf_eq.
- move=>->; case: eqP=>/eqP/chf_eq.
  - by move=>->; constructor.
  by move=>E; constructor; case=>En; rewrite En in E.
by move=>E; constructor; case=>En; rewrite En in E.
Qed.
*)
(** * Tensor product *)

(** ** Definition *)

Program Definition cstens (A B : space) : space :=
  {|
    token := token A * token B;
    chf '(a1, b1) '(a2, b2) := prod4 (chf a1 a2) (chf b1 b2);
  |}.
Next Obligation.
move=>A B [a1 b1][a2 b2].
by rewrite (chf_symm _ a2 a1) (chf_symm _ b2 b1).
Qed.
(*
Next Obligation.
move=>A B [a b]=>/=.
by move/eqP: (chf_ub _ a)=>->; move/eqP: (chf_ub _ b)=>->/=.
Qed.
*)
(*
Next Obligation.
move=>A B [a1 b1][a2 b2].
case E1: (chf a1 a2)=>/=.
- have/chf_eq {}E1: chf a1 a2 != Eq by rewrite E1.
  by case E2: (chf b1 b2)=>/=; constructor; case=>A1; rewrite A1 in E1.
- move/eqP/chf_eq: E1=>->.
  case E2: (chf b1 b2)=>/=; constructor.
  - have/chf_eq {}E2: chf b1 b2 != Eq by rewrite E2.
    by case=>A2; rewrite A2 in E2.
  - by move/eqP/chf_eq: E2=>->.
  have/chf_eq {}E2: chf b1 b2 != Eq by rewrite E2.
  by case=>A2; rewrite A2 in E2.
have/chf_eq {}E1: chf a1 a2 != Eq by rewrite E1.
by case E2: (chf b1 b2)=>/=; constructor; case=>A1; rewrite A1 in E1.
Qed.
*)
Infix "*" := cstens : chf_scope.

(** ** Functoriality *)

Program Definition cstens_lmap {A B C D} (f : A --o B) (g : C --o D) : A*C --o B*D :=
  {|
    has '((a, c), (b, d)) := has f (a, b) /\ has g (c, d);
  |}.
Next Obligation.
move=>A B C D f g [[a1 c1][b1 d1]][[a2 c2][b2 d2]][Hab1 Hcd1][Hab2 Hcd2] /=.
move: (has_coh _ _ _ _ Hcd1 Hcd2)=>/=.
move: (has_coh _ _ _ _ Hab1 Hab2)=>/=.
by exact: coh_imp_prod.
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
    chf x y := Unit;
  |}.
(*
Next Obligation.
by move=>[][]; case: eqP=>//; constructor.
Qed.
*)
Notation "1" := csunit : chf_scope.

(** Left unitor *)

Program Definition lam A : 1 * A --o A :=
  {|
     has '((_, a), b) := a = b;
  |}.
Next Obligation.
by move=>A [[[] a1] b1][[[] a2] b2] /= ->->; case: (chf b1 b2).
Qed.

(** Right unitor *)

Program Definition rho A : A * 1 --o A :=
  {|
  has '((a, _), b) := a = b;
  |}.
Next Obligation.
move=>A [[a1 []] b1][[a2 []] b2] /= ->->.
by rewrite prod_eql; exact: coh_imp_refl.
Qed.

(* etc.. *)

(** ** Negation *)

(** To avoid confusion between the [coh] relation associated with [A]
  and [lneg A], we introduce this singleton type. *)

Variant lneg_token A :=
  | ln (a : token A).

Arguments ln {A}.

Program Definition lneg (A : space) : space :=
  {|
    token := lneg_token A;
    chf '(ln x) '(ln y):= neg4 (chf x y);
  |}.
Next Obligation.
by move=>A [x][y]; rewrite chf_symm.
Qed.
(*
Next Obligation.
move=>A [a]/=.
move/eqP: (chf_ub _ a)=>->/=. move/eqP: (chf_ub _ b)=>->/=.
Qed.
*)
(*
Next Obligation.
move=>A [x][y]; case E: (chf x y)=>/=; constructor.
- have/chf_eq {E}En: chf x y != Eq by rewrite E.
  by case.
- by move/eqP/chf_eq: E=>->.
have/chf_eq {E}En: chf x y != Eq by rewrite E.
by case.
Qed.
*)
Program Definition lmap_flip {A B} (f : A --o B) : lneg B --o lneg A :=
  {|
    has '((ln x), (ln y)) := has f (y, x);
  |}.
Next Obligation.
move=>A B f [[b1 [a1]] [[b2][a2]]] H1 H2 /=.
move: (has_coh _ _ _ _ H1 H2)=>/=.
by exact: coh_imp_neg.
Qed.

Program Definition neg_inv_t {A} : A --o lneg (lneg A) :=
  {|
    has '(a, ln (ln b)) := a = b;
  |}.
Next Obligation.
move=>A [a1 [[b1]]][a2 [[b2]]] {a1}->{a2}->/=.
by rewrite neg_inv; exact: coh_imp_refl.
Qed.

Program Definition neg_inv_f {A} : lneg (lneg A) --o A :=
  {|
    has '(ln (ln a), b) := a = b;
  |}.
Next Obligation.
move=>A [[[a1]] b1][[[a2]] b2] {a1}->{a2}->/=.
by rewrite neg_inv; exact: coh_imp_refl.
Qed.

(** * Cartesian structure *)

(** ** Binary product *)

(** *** Definition *)

Program Definition csprod (A B : space) : space :=
  {|
    token := token A + token B;
    chf a b := match a, b with
               | inl x, inl y => chf x y
               | inr x, inr y => chf x y
               | _    , _     => Coh
               end
  |}.
Next Obligation.
by move=>A B [x|x][y|y] //=; rewrite chf_symm.
Qed.
(*
Next Obligation.
move=>A B; case=>a; case=>b; try by constructor.
- case H: (chf a b); constructor.
  - have/chf_eq {}H: chf a b != Eq by rewrite H.
    by case.
  - by move/eqP/chf_eq: H=>->.
  have/chf_eq {}H: chf a b != Eq by rewrite H.
  by case.
case H: (chf a b); constructor.
- have/chf_eq {}H: chf a b != Eq by rewrite H.
  by case.
- by move/eqP/chf_eq: H=>->.
have/chf_eq {}H: chf a b != Eq by rewrite H.
by case.
Qed.
*)
Infix "&&" := csprod : chf_scope.

Program Definition csp1 {A B : space} : A && B --o A :=
  {|
    has '(x, a) := inl a = x;
  |}.
Next Obligation.
move=>A B [a1 b1][a2 b2] /= <-<-.
by exact: coh_imp_refl.
Qed.

Program Definition csp2 {A B : space} : A && B --o B :=
  {|
    has '(x, b) := inr b = x;
  |}.
Next Obligation.
move=>A B [a1 b1][a2 b2] /= <-<-.
by exact: coh_imp_refl.
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
move=>X A B f g /= [a1 b1][a2 b2]; case: b2=>b2; case: b1=>b1 H1 H2.
- by move: (has_coh _ _ _ _ H1 H2).
- by exact: coh_imp_coh.
- by exact: coh_imp_coh.
by move: (has_coh _ _ _ _ H1 H2).
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

Program Definition cssum (A B : space) : space :=
  {|
    token := token A + token B;
    chf a b := match a, b with
               | inl x, inl y => chf x y
               | inr x, inr y => chf x y
               | _    , _     => Incoh
               end
  |}.
Next Obligation.
by move=>A B; case=>x; case=>y //; rewrite chf_symm.
Qed.
(*
Next Obligation.
move=>A B; case=>x; case=>y; try by [constructor];
case: (@eqP _ (chf x y))=>H; constructor.
- by move/eqP/chf_eq: H=>->.
- by case=>E; rewrite E in H; move/eqP/chf_eq: H.
- by move/eqP/chf_eq: H=>->.
by case=>E; rewrite E in H; move/eqP/chf_eq: H.
Qed.
*)
Infix "+" := cssum : chf_scope.

Program Definition csi1 {A B : space} : A --o A + B :=
  {|
    has '(a, x) := inl a = x;
  |}.
Next Obligation.
move=>A B [a1 _][a2 _]<-<-/=.
by exact: coh_imp_refl.
Qed.

Program Definition csi2 {A B : space} : B --o A + B :=
  {|
    has '(b, x) := inr b = x;
  |}.
Next Obligation.
move=>A B [a1 _][a2 _]<-<-/=.
by exact: coh_imp_refl.
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
move=>A B X f g [ab1 x1][ab2 x2] /=.
case: ab1=>[a1|b1]; case: ab2=>[a2|b2] //= H1 H2;
by move: (has_coh _ _ _ _ H1 H2).
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

(** ** Terminal object, 0 = top *)

(** *** Definition *)

Program Definition csterm : space :=
  {|
    token := Empty_set;
    chf x y := Coh;
  |}.
(*Next Obligation. by []. Qed.*)

Program Definition prod_unitl A : csterm && A --o A :=
  {|
     has '(a, b) := match a with
                    | inl x => Empty_set_rect _ x
                    | inr y => y = b
                    end
  |}.
Next Obligation.
move=>A [[|a1] b1] // [[|a2] b2] //= ->->.
by exact: coh_imp_refl.
Qed.

Program Definition prod_unitr A : A && csterm --o A :=
  {|
     has '(a, b) := match a with
                    | inl x => x = b
                    | inr y => Empty_set_rect _ y
                    end
  |}.
Next Obligation.
move=>A [[a1|] b1] // [[a2|] b2] //= ->->.
by exact: coh_imp_refl.
Qed.

Program Definition sum_unitl A : csterm + A --o A :=
  {|
     has '(a, b) := match a with
                    | inl x => Empty_set_rect _ x
                    | inr y => y = b
                    end
  |}.
Next Obligation.
move=>A [[|a1] b1] // [[|a2] b2] //= ->->.
by exact: coh_imp_refl.
Qed.

Program Definition sum_unitr A : A + csterm --o A :=
  {|
     has '(a, b) := match a with
                    | inl x => x = b
                    | inr y => Empty_set_rect _ y
                    end
  |}.
Next Obligation.
move=>A [[a1|] b1] // [[a2|] b2] //= ->->.
by exact: coh_imp_refl.
Qed.

(** *** Universal property *)

Program Definition discard A : A --o csterm :=
  {|
    has '(x, y) := False;
  |}.
Next Obligation. by move=>A [a1 b1][a2 b2]. Qed.

Lemma discard_uniq {A} (f : A --o csterm) :
  f = discard A.
Proof. by apply: lmap_ext=>x. Qed.

(** bottom *)

Program Definition csbot : space :=
  {|
    token := unit;
    chf x y := Bot;
  |}.

(* par *)

Program Definition cspar (A B : space) : space :=
  {|
    token := token A * token B;
    chf '(a1, b1) '(a2, b2) := par4 (chf a1 a2) (chf b1 b2);
  |}.
Next Obligation.
move=>A B [a1 b1][a2 b2].
by rewrite chf_symm (chf_symm _ b1).
Qed.
(*
Next Obligation.
move=>A B [a1 b1][a2 b2]; case H1: (chf a1 a2)=>/=.
- have/chf_eq {}H1: chf a1 a2 != Eq by rewrite H1.
  by constructor; case.
- move/eqP/chf_eq: H1=>->.
  case H2: (chf b1 b2)=>/=; constructor.
  - have/chf_eq {}H2: chf b1 b2 != Eq by rewrite H2.
    by case.
  - by move/eqP/chf_eq: H2=>->.
  have/chf_eq {}H2: chf b1 b2 != Eq by rewrite H2.
  by case.
have/chf_eq {}H1: chf a1 a2 != Eq by rewrite H1.
by case H2: (chf b1 b2)=>/=; constructor; case.
Qed.
*)
Program Definition lunit A : (cspar csbot A) --o A :=
  {|
     has '((_, a), b) := a = b;
  |}.
Next Obligation.
by move=>A [[[] a1] b1][[[] a2] b2] /= ->->; case: (chf b1 b2).
Qed.

(** Right unitor *)

Program Definition runit A : (cspar A csbot) --o A :=
  {|
  has '((a, _), b) := a = b;
  |}.
Next Obligation.
move=>A [[a1 []] b1][[a2 []] b2] /= ->->.
by rewrite par_eql; exact: coh_imp_refl.
Qed.


(** * Sequential constructions *)

(** ** Composition *)
(*
Program Definition sequ (A B : space) : space :=
  {|
    token := token A * token B;
    chf '(a1, b1) '(a2, b2) := seq3 (chf a1 a2) (chf b1 b2);
  |}.
Next Obligation.
move=>A B [a1 b1][a2 b2].
by rewrite chf_symm (chf_symm _ b1).
Qed.
Next Obligation.
move=>A B [a1 b1][a2 b2]; case H1: (chf a1 a2)=>/=.
- have/chf_eq {}H1: chf a1 a2 != Eq by rewrite H1.
  by constructor; case.
- move/eqP/chf_eq: H1=>->.
  case H2: (chf b1 b2)=>/=; constructor.
  - have/chf_eq {}H2: chf b1 b2 != Eq by rewrite H2.
    by case.
  - by move/eqP/chf_eq: H2=>->.
  have/chf_eq {}H2: chf b1 b2 != Eq by rewrite H2.
  by case.
have/chf_eq {}H1: chf a1 a2 != Eq by rewrite H1.
by constructor; case.
Qed.

Infix ";;" := sequ (at level 40, left associativity) : chf_scope.

Program Definition sequ_lmap {A B C D} (f : A --o B) (g : C --o D) :
    (A ;; C) --o (B ;; D) :=
  {|
    has '((a, c), (b, d)) := has f (a, b) /\ has g (c, d);
  |}.
Next Obligation.
move=>A B C D f g [[a1 c1][b1 d1]][[a2 c2][b2 d2]] /=
  [Hab1 Hcd1][Hab2 Hcd2].
move: (has_coh _ _ _ _ Hcd1 Hcd2)=>/=.
move: (has_coh _ _ _ _ Hab1 Hab2)=>/=.
by exact: coh_imp_seq.
Qed.

Infix ";;" := sequ_lmap : lmap_scope.
*)
(** ** Exponential *)

(* finite clique *)

Fixpoint seq_chf {A} (xs ys : seq (token A)) : four :=
  match xs, ys with
  | [::], _ => Coh
  | _, [::] => Coh
  | x::s1, y::s2 => match chf x y with
                    | Coh => Coh
                    | Incoh => Incoh
                    | _ => seq_chf s1 s2
                    end
  end.


(*
Lemma seq_chf_eq {A} : Equality.axiom (fun a b : seq (token A) => seq_chf a b == Eq).
Proof.
elim=>[|x s1 IH1]; case=>[|y s2] /=; try by constructor.
case H: (chf x y).
- have/chf_eq {}H: chf x y != Eq by rewrite H.
  by constructor; case.
- move/eqP/chf_eq: H=>->.
  by apply: iffP; first by [apply: IH1]; [move=>-> | case].
have/chf_eq {}H: chf x y != Eq by rewrite H.
by constructor; case.
Qed.
*)
Program Definition dag (A : space) : space :=
  {|
    token := seq (token A);
    chf := seq_chf;
  |}.
Next Obligation.
move=>A s t; elim: s t=>[|x s1 IH1] /=; first by case.
by case=>//= y s2; rewrite chf_symm; case: (chf y x).
Qed.
(*
Next Obligation.
move=>A; exact: seq_chf_eq.
Qed.
*)
Notation "! A" := (dag A)
  (at level 8, right associativity, format "'!' A") : chf_scope.

(** *** Comonad structure *)
(*
Lemma cat_coh {A} (s : seq (token A)) t1 t2 :
  seq_chf (s ++ t1) (s ++ t2) = seq_chf t1 t2.
Proof.
by elim: s.
(*
elim: s=>//= x s H.
by move/chf_eq/eqP: (erefl x)=>->.
*)
Qed.
*)
Lemma cat_incoh {A} (s1 s2 : seq (token A)) t1 t2 :
  seq_chf s1 s2 = Incoh ->
  seq_chf (s1 ++ t1) (s2 ++ t2) = Incoh.
Proof.
elim: s1 s2 =>[|x1 s1 IH]; case =>//= x2 s2.
by case: (chf x1 x2)=>//; apply: IH.
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
move=>A B f /= [aa1 bb1][aa2 bb2] Hab1 Hab2.
elim: aa1 bb1 aa2 bb2 Hab1 Hab2=>[|a1 aa1 IH] bb1 aa2 bb2.
- by move=>/dag_lmaps_lnil->.
case/dag_lmaps_lcons=>[b1][bb1'][{bb1}-> H1 Hd1] /=.
case: aa2=>[|a2 aa2]; first by move=>/dag_lmaps_lnil->.
case/dag_lmaps_lcons=>[b2][bb2'][{bb2}-> H2 Hd2].
move: (has_coh _ _ _ _ H1 H2)=>/=.
case E1: (chf a1 a2)=>//=; case E2: (chf b1 b2)=>//= _.
- apply: coh_imp_coh.
- by apply: IH.
- apply: coh_imp_coh.
- by apply: IH.
by apply: IH.
Qed.


(*
- move=>/dag_lmaps_lnil->/=.
  case: aa2=>/=.
  - by move=>/dag_lmaps_lnil->.
  by move=>a2 aa2 /dag_lmaps_lcons [b2][bb2'][->].
case/dag_lmaps_lcons=>[b1][bb1'][{bb1}-> H1 Hd1] /=.
case: aa2=>[|a2 aa2]; first by move=>/dag_lmaps_lnil->.
case/dag_lmaps_lcons=>[b2][bb2'][{bb2}-> H2 Hd2].
move: (has_coh _ _ _ _ H1 H2)=>/=.
by case E1: (chf a1 a2)=>//=; case E2: (chf b1 b2)=>//= _; apply: IH.
(*- by apply: coh_imp_coh.
by apply: IH.*)
Qed.
*)
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

Variant dag_counit_lmaps A : token !A -> token A -> Prop :=
  dag_counit_intro a : dag_counit_lmaps A [::a] a.

(* aka dereliction *)

(* TODO stuck here *)
(* seq_chf [::x][::y] should be = chf x y for this to work *)
(* this implies we should backtrack on reaching [::] and combine values *)
(* but how to combine e.g. bot and unit? *)
(*
Program Definition dag_counit A : !A --o A :=
  {|
    has '(aa, a) := dag_counit_lmaps A aa a;
  |}.
Next Obligation.
move=>A /= [x1 _][x2 _][t1][t2] /=.
case: (chf t1 t2).
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
move=>A /= [a1 aa1][a2 aa2] H1 H2.
elim: aa1 aa2 a1 a2 H1 H2=>[|x1 aa1 IH] aa2 a1 a2.
- move/dag_comult_rnil=>->.
  case: aa2.
  - by move/dag_comult_rnil=>->.
  by move=>x2 aa2 _; apply: coh_imp_coh.
case/dag_comult_rcons=>s1[{a1}-> H1].
case: aa2=>[|x2 aa2].
- by move=>_ /=; exact: coh_imp_coh.
case/dag_comult_rcons=>s2[{a2}-> H2] /=.
move: (IH _ _ _ H1 H2)=>H.
case E: (seq_chf x1 x2).
- by exact: coh_imp_coh.
- move/eqP/seq_chf_eq: E=>->.
  by rewrite cat_coh.
by rewrite cat_incoh.
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
*)