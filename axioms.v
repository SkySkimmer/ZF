Set Implicit Arguments.
Unset Strict Implicit.

Require Export tactics.

Module Axioms.
Require Import Arith.
Require Import List.

Parameter E : Type.

Notation E1 := (E -> E).
Notation E2 := (E -> E1).
Notation E3 := (E -> E2).
Notation E4 := (E -> E3).
Notation E5 := (E -> E4).
Notation E6 := (E -> E5).
(** thus for example E3 = E -> E -> E -> E **)

Fixpoint En (n : nat) : Type := match n with
  | 0 => E
  | S k => E -> En k
  end.

Notation EP := (E -> Prop).
Notation E2P := (E -> EP).
Notation E3P := (E -> E2P).
Notation E4P := (E -> E3P).

Fixpoint EnP (n : nat) := match n with
  | 0 => Prop
  | S k => E -> EnP k
  end.

Parameter inc : E -> E -> Prop.

Definition sub x y := forall a, inc a x -> inc a y.

Notation "a ∈ b" := (inc a b) (no associativity, at level 98).
Notation "a ∉ b" := (~ inc a b) (no associativity, at level 98).
Notation "a ⊂ b" := (sub a b) (no associativity, at level 98).

Lemma sub_refl : forall x, sub x x.
Proof.
ir;uhg;ir;am.
Qed.

Lemma sub_trans : forall x y, sub x y -> forall z, sub y z -> sub x z.
Proof.
ir;uhg;ir. ap H0;au.
Qed.

Axiom extensionality : forall x y, sub x y -> sub y x -> x=y.

(*** we also need extensionality for general product types ***)

(***) Axiom
        prod_extensionality :
          forall (x : Type) (y : x -> Type) (u v : forall a : x, y a),
          (forall a : x, u a = v a) -> u = v.

Lemma arrow_extensionality :
 forall (x y : Type) (u v : x -> y), (forall a : x, u a = v a) -> u = v.
Proof.
intros x y.
change
  (forall u v : forall a : x, (fun i : x => y) a,
   (forall a : x, u a = v a) -> u = v) in |- *.
intros. apply prod_extensionality. assumption.
Qed. 


(*axiom of choice*)

Inductive nonemptyT (t : Type) : Prop :=
    nonemptyT_intro : t -> nonemptyT t.

(***) Parameter chooseT : forall (t : Type) (p : t -> Prop), nonemptyT t -> t.
(***) Axiom
        chooseT_pr :
          forall (t : Type) (p : t -> Prop) (ne : nonemptyT t),
          ex p -> p (chooseT p ne).

Axiom nonemptyE : nonemptyT E.

Definition choose : EP -> E.
ir. ap chooseT. exact X. exact nonemptyE.
Defined.

Lemma choose_pr : forall p, ex p -> p (choose p).
Proof.
ir. uf choose. ap chooseT_pr. am.
Qed.

(*** the following actually follow from the above as was shown in the
standard library but we write them as axioms for brevity **************)

(***) Axiom excluded_middle : forall P : Prop, ~ ~ P -> P.
(***) Axiom proof_irrelevance : forall (P : Prop) (q p : P), p = q.

(*** the following axioms can be obtained from the Ensembles library but we include it here
as an axiom; it is used for convenience, allowing us to replace iff by equality so as to
be able to rewrite using equality of propositions **********************************)

(***) Axiom iff_eq : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P = Q.


(*by_cases*)

Lemma p_or_not_p : forall P : Prop, P \/ ~ P.
Proof.
ir.
eapply excluded_middle.
unfold not in |- *.
ir.
assert P; ap excluded_middle; unfold not in |- * ; au.
Qed.

Definition by_cases_pr (T : Type) (P : Prop) (a : P -> T) 
  (b : ~ P -> T) (x : T) :=
  and (forall p : P, a p = x) (forall q : ~ P, b q = x).

Lemma by_cases_exists :
 forall (T : Type) (P : Prop) (a : P -> T) (b : ~ P -> T),
 exists x : T, by_cases_pr a b x.
Proof.
ir. assert (P \/ ~ P). ap p_or_not_p. nin H.
eapply ex_intro with (a H). unfold by_cases_pr in |- *. xd.
ir. assert (H = p). ap proof_irrelevance. rewrite H0. tv.
ir. pose (q H). elim f.
eapply ex_intro with (b H). unfold by_cases_pr in |- *. xd.
ir. pose (H p). elim f.
ir. assert (H = q). ap proof_irrelevance. rewrite H0. tv.
Qed.

Lemma by_cases_nonempty :
 forall (T : Type) (P : Prop) (a : P -> T) (b : ~ P -> T), nonemptyT T.
Proof.
ir.
ir. assert (P \/ ~ P). ap p_or_not_p. nin H.
eapply nonemptyT_intro. exact (a H).
eapply nonemptyT_intro. exact (b H).
Qed.



Definition by_cases (T : Type) (P : Prop) (a : P -> T) 
  (b : ~ P -> T) :=
  chooseT (fun x : T => by_cases_pr a b x) (by_cases_nonempty a b).


Lemma by_cases_property :
 forall (T : Type) (P : Prop) (a : P -> T) (b : ~ P -> T),
 by_cases_pr a b (by_cases a b).
Proof.
ir.
cp (by_cases_exists a b).
cp (by_cases_nonempty a b).
cp (chooseT_pr H0 H).
unfold by_cases in |- *.
assert (by_cases_nonempty a b = H0).
ap proof_irrelevance.
rewrite H2.
am.
Qed.

Lemma by_cases_unique :
 forall (T : Type) (P : Prop) (a : P -> T) (b : ~ P -> T) (x : T),
 by_cases_pr a b x -> by_cases a b = x.
Proof.
ir.
cp (by_cases_property a b).
ir. assert (P \/ ~ P). ap p_or_not_p. nin H1.
unfold by_cases_pr in H.  unfold by_cases_pr in H0.  xd.
transitivity (a H1). sy. au. au.
unfold by_cases_pr in H.  unfold by_cases_pr in H0.  xd.
transitivity (b H1). sy. au. au.
Qed.


Lemma by_cases_if :
 forall (T : Type) (P : Prop) (a : P -> T) (b : ~ P -> T) (p : P),
 by_cases a b = a p.
Proof.
ir. eapply by_cases_unique.
unfold by_cases_pr in |- *. xd.
ir. assert (p = p0). ap proof_irrelevance. rewrite H. tv.
ir. cp (q p). elim H.
Qed.

Lemma by_cases_if_not :
 forall (T : Type) (P : Prop) (a : P -> T) (b : ~ P -> T) (q : ~ P),
 by_cases a b = b q.
Proof.
ir. eapply by_cases_unique.
unfold by_cases_pr in |- *. xd.
ir.
cp (q p). elim H.
ir. assert (q = q0). ap proof_irrelevance. rewrite H. tv.
Qed.

(*Paire*)

Parameter doubleton : E2.

Axiom doubleton_pr : forall a b x, inc x (doubleton a b) = (x=a \/ x=b).

Lemma doubleton_or : forall a b x, inc x (doubleton a b) -> x=a\/x=b.
Proof.
ir. wr doubleton_pr. am.
Qed.

Lemma doubleton_inc : forall a b x, (x = a \/ x = b) -> inc x (doubleton a b).
Proof.
ir. rw doubleton_pr. am.
Qed.

Lemma doubleton_l : forall a b, inc a (doubleton a b).
Proof.
ir. rw doubleton_pr;au.
Qed.

Lemma doubleton_r : forall a b, inc b (doubleton a b).
Proof.
ir;rw doubleton_pr;au.
Qed.

Definition singleton a := doubleton a a.

Lemma singleton_inc : forall a, inc a (singleton a).
Proof.
ir. ap doubleton_l.
Qed.

Lemma singleton_eq : forall a x, inc x (singleton a) -> x=a.
Proof.
ir.
apply doubleton_or in H. nin H;am.
Qed.

Lemma singleton_rw : forall a x, inc x (singleton a) = (x=a).
Proof.
ir;ap iff_eq.
ap singleton_eq.
ir;subst. ap singleton_inc.
Qed.

Lemma doubleton_comm : forall a b, doubleton a b = doubleton b a.
Proof.
ir. ap extensionality;uhg;ir.
apply doubleton_or in H;ap doubleton_inc. nin H;au.
apply doubleton_or in H;ap doubleton_inc. nin H;au.
Qed.

Lemma doubleton_eq : forall a b c d, (doubleton a b = doubleton c d) = ((a=c & b=d)\/(a=d & b=c)).
Proof.
ir;ap iff_eq;ir.
assert (inc c (doubleton a b)). rw H. ap doubleton_l.
apply doubleton_or in H0. nin H0;subst.
assert (inc d (doubleton a b)). rw H. ap doubleton_r.

apply doubleton_or in H0;nin H0;subst.
assert (inc b (doubleton a a)).
wr H. ap doubleton_r.
apply singleton_eq in H0. subst. au.
au.

assert (inc d (doubleton a b)).
rw H. ap doubleton_r. apply doubleton_or in H0;nin H0;subst;au.
left. ee. ap singleton_eq.
uf singleton. wr H. ap doubleton_l. tv.

nin H;ee;subst.
tv. ap doubleton_comm.
Qed.

Lemma singleton_inj : forall a b, singleton a = singleton b -> a=b.
Proof.
ir. ap singleton_eq. wr H. ap singleton_inc.
Qed.


Parameter Z :  E -> EP -> E.

Axiom Z_rw : forall a p x, inc x (Z a p) = (inc x a & p x).

Lemma Z_inc : forall a (p:EP) x, inc x a -> p x -> inc x (Z a p).
Proof.
ir. rw Z_rw. ee;am.
Qed.

Lemma Z_all : forall a p x, inc x (Z a p) -> (inc x a & p x).
Proof.
ir;wr Z_rw;am.
Qed.

Lemma Z_sub : forall a p, sub (Z a p) a.
Proof.
ir;uhg;ir. apply Z_all in H. am.
Qed.

Lemma Z_pr : forall a p x, inc x (Z a p) -> p x.
Proof.
ir;eapply Z_all. am.
Qed.

Ltac Ztac := 
  match goal with
  | id1:(inc ?X1 (Z _ _)) |- _ => apply Z_all in id1;nin id1
  |  |- (inc _ (Z _ _)) => ap Z_inc
  | _ => idtac
  end.

Lemma no_total_set : ~ exists x, forall y, inc y x.
Proof.
uhg;ir;nin H.
pose (z := Z x (fun y => ~ inc y y)).
assert (inc z z = ~ inc z z).
ap iff_eq;ir.
ufa z. Ztac. am.
ap Z_inc. ap H. am.

assert (~ inc z z).
uhg;ir. cp H1. rwi H0 H2. au.
ap H1. rw H0. am.
Qed.

Lemma always_other : forall x, exists y, ~ inc y x.
Proof.
ir;ap excluded_middle;uhg;ir.
ap no_total_set.
exists x. ir.
ap excluded_middle;uhg;ir.
ap H. exists y;am.
Qed.

Definition complement a b := Z a (fun x => ~ inc x b).

Lemma use_complement : forall a b x, inc x a -> ~ inc x (complement a b) -> inc x b.
Proof.
ir. ap excluded_middle;uhg;ir.
ap H0. ap Z_inc;am.
Qed.


Parameter union : E1.

Axiom union_rw : forall a x, inc x (union a) = (exists y, inc y a & inc x y).

Notation "⋃" := union.

Lemma union_inc : forall a x, (exists y, inc y a & inc x y) -> inc x (union a).
Proof.
ir;rw union_rw;am.
Qed.

Lemma union_ex : forall a x, inc x (union a) -> (exists y, inc y a & inc x y).
Proof.
ir;wr union_rw;am.
Qed.

Definition union2 a b := union (doubleton a b).

Lemma union2_or : forall a b x, inc x (union2 a b) -> (inc x a \/ inc x b).
Proof.
ir.
apply union_ex in H. nin H;ee. apply doubleton_or in H.
nin H;subst;au.
Qed.

Lemma union2_inc : forall a b x, (inc x a \/ inc x b) -> inc x (union2 a b).
Proof.
ir.
ap union_inc. nin H.
exists a;ee. ap doubleton_l. am.
exists b;ee. ap doubleton_r. am.
Qed.

Lemma union2_l : forall a b, sub a (union2 a b).
Proof.
uhg;ir. ap union_inc. exists a;ee. ap doubleton_l. am.
Qed.

Lemma union2_r : forall a b, sub b (union2 a b).
Proof.
uhg;ir;ap union_inc;exists b;ee;try am;ap doubleton_r.
Qed.

Lemma union2_rw : forall a b x, inc x (union2 a b) = (inc x a \/ inc x b).
Proof.
ir;ap iff_eq. ap union2_or. ap union2_inc.
Qed.

Definition tack_on a b := union2 a (singleton b).

Lemma tack_on_or : forall x y z : E, inc z (tack_on x y) ->
(inc z x \/ z = y). 
Proof. 
ir. ufi tack_on H. cp (union2_or H). nin H0.
Proof.
ap or_introl; am. ap or_intror. ap singleton_eq; am. 
Qed. 

Lemma tack_on_inc: forall x y z:E,
(inc z (tack_on x y) ) = (inc z x \/ z = y).
Proof.
ir. ap iff_eq. ir; ap tack_on_or. am. ir.
nin H. uf tack_on. ap union2_l. am.
uf tack_on. ap union2_r. rw H. 
ap singleton_inc. 
Qed.

Definition inter  : E -> E.
intros a.
ap Z. exact (union a).
ir. exact (forall x', inc x' a -> inc X x').
Defined.

Notation "⋂" := inter.

Definition emptyset : E.
exact (choose (fun x => forall y, ~ inc y x)).
Defined.

Notation "∅" := emptyset.

Lemma emptyset_empty : forall x, ~ inc x emptyset.
Proof.
uf emptyset. ap choose_pr.
destruct nonemptyE.
exists (complement X X).
ir. uhg;ir;ufa complement;Ztac.
au.
Qed.

Lemma emptyset_sub_all : forall x, sub emptyset x.
Proof.
ir;uhg;ir. apply emptyset_empty in H. elim H.
Qed.

Lemma empty_emptyset : forall x, (forall y, inc y x -> False) -> x = emptyset.
Proof.
ir;ap extensionality.
uhg;ir. elim (H a H0).
ap emptyset_sub_all.
Qed.

Lemma emptyset_sub_is : forall x, sub x emptyset -> x = emptyset.
Proof.
ir;ap extensionality. am. ap emptyset_sub_all.
Qed.

Lemma union_empty : union emptyset = emptyset.
Proof.
ap empty_emptyset. ir.
apply union_ex in H;nin H;ee. apply emptyset_empty with x;am.
Qed.

Definition nonempty x := exists y, inc y x.

Lemma nonempty_not_emptyset_rw : forall x, nonempty x = (x<> emptyset).
Proof.
uf nonempty. ir;ap iff_eq;ir.
uhg;ir;subst. nin H.
apply emptyset_empty in H. am.
ap excluded_middle;uhg;ir.
ap H. ap empty_emptyset. ir. ap H0. exists y;am.
Qed.

Lemma inter_empty : inter emptyset  = emptyset.
Proof.
ap emptyset_sub_is. eapply sub_trans. ap Z_sub.
rw union_empty. ap sub_refl.
Qed.

Lemma inter_rw : forall a, nonempty a -> forall x, inc x (inter a) = (forall y, inc y a -> inc x y).
Proof.
ir. uf inter.
ap iff_eq;ir.
apply Z_all in H0;nin H0.
apply union_ex in H0;nin H0;ee.
ap H2. am.

ap Z_inc. ap union_inc. nin H.
exists x0. ee. am. au.
am.
Qed.

Lemma inter_inc : forall a, nonempty a -> forall x, (forall y, inc y a -> inc x y) -> 
inc x (inter a).
Proof.
ir;rw inter_rw. am. am.
Qed.

Lemma inter_all : forall a x, inc x (inter a) -> forall y, inc y a -> inc x y.
Proof.
ir.
apply Z_all in H. ee.
au.
Qed.

Definition inter2 a b := inter (doubleton a b).

Lemma inter2_rw : forall a b x, inc x (inter2 a b) = (inc x a & inc x b).
Proof.
ir. uf inter2. rw inter_rw.
ap iff_eq;ir.
ee;ap H. ap doubleton_l. ap doubleton_r.
apply doubleton_or in H0. nin H0;subst;am.
econstructor. ap doubleton_l.
Qed.

Lemma inter2_inc : forall a b x, inc x a -> inc x b -> inc x (inter2 a b).
Proof.
ir. rw inter2_rw. ee;am.
Qed.

Lemma inter2_and : forall a b x, inc x (inter2 a b) -> (inc x a & inc x b).
Proof.
ir. wr inter2_rw. am.
Qed.




Parameter powerset : E1.

Axiom powerset_rw : forall a x, inc x (powerset a) = sub x a.

Lemma powerset_sub : forall a x, inc x (powerset a) -> sub x a.
Proof.
ir. wr powerset_rw. am.
Qed.

Lemma powerset_inc : forall a x, sub x a -> inc x (powerset a).
Proof.
ir;rw powerset_rw;am.
Qed.

Lemma singleton_union : forall x, union (singleton x) = x.
Proof.
ir. ap extensionality;uhg;ir.
apply union_ex in H;nin H;ee. apply singleton_eq in H. subst. am.
ap union_inc. exists x. ee. ap singleton_inc. am.
Qed.

(*
Tuples
tuples are defined by a function create : list E -> E injective
a n-tuple is some x s.t. exists l, length l = n & x = create l
a pair is a 2-tuple
a relation is a set of pairs. for r relation, R r x y = inc (pair x y) r
a function is a functional relation
product a b = Im2 pair a b
then functions a -> b are subsets of product a b
if a is a tuple a1 ... an, we want pair (create (x1 ... xn)) y to be a tuple
then the function would be both a relation and a set of n+1-tuples
this makes defining morphisms later much easier :
 a morphism on a signature between 2 structures (= assignements for the structure)
is a function preserving relations, and therefore passes for the structure's functions

then we have:
0-tuple : [] -> emptyset
1-tuple : x -> ??
2-tuple : x y -> pair x y
forall n, n+1-tuple : (x)n y -> pair (x)n y

pair x y = pair (x)1 y
so 1-tuple = identity ? not possible :
      (x)1 = create [x] = x = create [x1 ; ... ; xn] even when x is n-tuple

maybe looking at product sets instead
() -> emptyset(or something)
(x) -> ??
(x*y) -> product x y = Im2 pair x y
(x1*...*xn*xn+1) -> product (x1...xn) xn+1
forall x ntuple y set, pair x y is n+1 tuple
(n>=1) n=0 -> no restr -> 1-tuple can be anything

so give up on full injectivity of create, only injective for same-length lists
*)


Definition adjoin a b := doubleton (singleton a) (doubleton a b).

Lemma adjoin_eq : forall a b c d, adjoin a b = adjoin c d -> (a=c & b=d).
Proof.
ir. ufi adjoin H;ufi singleton H.
repeat rwi doubleton_eq H.
nin H;ee;nin H;nin H0;ee;subst;au.
Qed.

Fixpoint create_tuple (l : list E) := match l with
  | nil => emptyset
  | x::nil => x
  | x::tl => adjoin (create_tuple tl) x
  end.

Lemma adjoin_nonempty : forall a b, nonempty (adjoin a b).
Proof.
ir. econstructor. ap doubleton_l.
Qed.

Lemma create_tuple_eq : forall l, l<>nil -> forall l', 
length l = length l' -> create_tuple l = create_tuple l' -> l=l'.
Proof.
intros l Hl;nin l;ir;nin l';simpl in *;tv.
inversion H. inversion H.
inversion H;subst. clear H.
destruct l;destruct l'.
subst;tv.
inversion H2. inversion H2.
apply adjoin_eq in H0. ee.
subst. ap uneq. ap IHl. uhg;ir. inversion H0.
am.
am.
Qed.

Definition pair a b := create_tuple (b::a::nil).

Inductive is_pair : E -> Prop := 
  | pair_is_pair : forall a b, is_pair (pair a b).

Lemma pair_eq_l : forall a b c d, pair a b = pair c d -> a=c.
Proof.
ir. apply create_tuple_eq in H.
inversion H;au.
uhg;ir. inversion H0.
tv.
Qed.

Lemma pair_eq_r : forall a b c d, pair a b = pair c d -> b=d.
Proof.
ir. apply create_tuple_eq in H. inversion H;subst.
tv.
uhg;ir;inversion H0. tv.
Qed.

Lemma pair_eq : forall a b c d, pair a b = pair c d -> (a=c & b=d).
Proof.
ir. apply create_tuple_eq in H;inversion H;subst. au.
uhg;ir;inversion H0. tv.
Qed.

Lemma pair_adjoin_eq : pair=adjoin.
Proof.
reflexivity. 
Qed.

Lemma tuple_pair_S : forall l, l<>nil -> forall x, 
create_tuple (x::l) = pair (create_tuple l) x.
Proof.
ir. simpl. destruct l. nin H;tv.
tv.
Qed.

(*
To prove that we made the right decisions we need to define 
arbitrary-arity relations, and how they are related to functions
see (some other file, not yet decided)
*)

Notation J := pair.

Definition unicity (T : Type) (p : T -> Prop) := (forall y, p y -> forall y', p y' -> y=y').

Definition is_functional (r:E2P) := forall x, ex (r x) & (unicity (r x)).

Parameter replacement : E2P -> E1.

Axiom replacement_rw : forall r, is_functional r -> 
forall x y, inc y (replacement r x) = exists x0, inc x0 x & r x0 y.

Lemma replacement_pr : forall r, is_functional r -> 
forall x y, inc y (replacement r x) <-> exists x0, inc x0 x & r x0 y.
Proof.
ir. rw replacement_rw;au. split;ir;am.
Qed.

Lemma replacement_ex : forall r, is_functional r -> 
forall x y, inc y (replacement r x) -> exists x0, inc x0 x & r x0 y.
Proof.
intros r H x y;eapply replacement_pr;am.
Qed.

Lemma replacement_inc : forall r, is_functional r -> 
forall x y, (exists x0, inc x0 x & r x0 y) -> 
inc y (replacement r x).
Proof.
intros r H x y;ap replacement_pr. am.
Qed.

Definition unique_choose (p : EP) : E.
ap union.
ap replacement.
ir. ap p. ap X0.
exact (singleton emptyset).
Defined.

Lemma unique_choose_pr : forall p, ex p -> 
(unicity p) -> 
p (unique_choose p).
Proof.
ir.
uf unique_choose.
assert (is_functional (fun _ X0 : E => p X0)).
uhg;ir;ee;ir. nin H;econstructor;am.
au.
cp (replacement_pr H1 (singleton emptyset)).
simpl in H2.
assert (forall y, inc y (replacement (fun _ X0 : E => p X0) (singleton ∅)) <->
p y).
ir;split;ir. apply H2 in H3. nin H3;am.
ap H2. exists emptyset. ee. ap singleton_inc. am.
nin H.
eapply eq_ind.
ap H.
ap extensionality;uhg;ir.
ap union_inc. econstructor. ee.
ap H3. ap H. am.
apply union_ex in H4;nin H4;ee.
apply H3 in H4.
eapply eq_ind. am.
au.
Qed.

Definition pr1 x := unique_choose (fun a => exists b, x = pair a b).
Definition pr2 x := unique_choose (fun b => exists a, x = pair a b).

(*
Definition pr1 x := choose (fun a => exists b, x = pair a b).
Definition pr2 x := choose (fun b => exists a, x = pair a b).
*)

Notation P := pr1.
Notation Q := pr2.


Lemma pr1_pr : forall a b, pr1 (pair a b) = a.
Proof.
ir. assert (exists b', J a b = J (P (J a b)) b'). uf P. ap unique_choose_pr.
exists a;exists b;tv.
uhg;ir. nin H;nin H0. apply pair_eq in H;apply pair_eq in H0;ee;subst;tv.
nin H. apply pair_eq in H;ee;au.
Qed.

Lemma pr2_pr : forall a b, pr2 (pair a b) = b.
Proof.
ir. assert (exists a', J a b = J a' (Q (J a b))). uf Q. ap unique_choose_pr.
exists b;exists a;tv.
uhg;ir. nin H;nin H0. apply pair_eq in H;apply pair_eq in H0;ee;subst;tv.
nin H. apply pair_eq in H;ee;au.
Qed.

Ltac clpr := repeat (first [rw pr1_pr | rw pr2_pr]).

Ltac clpri H := repeat (first [rwi pr1_pr H | rwi pr2_pr H]).

Lemma pair_recov : forall x, is_pair x -> x = pair (P x) (Q x).
Proof.
ir. nin H.  clpr. tv.
Qed.

Definition Im f x := replacement (fun a b => b = f a) x.

Lemma Im_rw : forall f a y, inc y (Im f a) = (exists x, inc x a & y = f x).
Proof.
ir. uf Im. rw replacement_rw.
tv. uhg;ir;ee.
exists (f x);tv.
uhg;ir;subst;au.
Qed.

Lemma Im_inc : forall f a x, inc x a -> inc (f x) (Im f a).
Proof.
ir.
rw Im_rw. exists x;ee;au.
Qed.

Lemma Im_show_inc : forall f a y, (exists x, inc x a & y = f x) -> inc y (Im f a).
Proof.
ir. rw Im_rw. am.
Qed.

Lemma Im_ex : forall f a y, inc y (Im f a) -> exists x, inc x a & y = f x.
Proof.
ir. wr Im_rw. am.
Qed.
(*note: getting replacement from Im uses choice, but Im from replacement 
doesn't*)


Definition Im2 (f : E2) (x y : E) := union (Im (fun a => Im (fun b => f a b) y) x).

Lemma Im2_rw : forall f x y z, inc z (Im2 f x y) = exists a, exists b, inc a x & inc b y & z = f a b.
Proof.
ir;ap iff_eq;ir.
apply union_ex in H. nin H. ee.
apply Im_ex in H;nin H. ee.
subst. apply Im_ex in H0;nin H0;ee. subst. exists x1;exists x0;ee;au.
nin H;nin H;ee;subst.
ap union_inc. econstructor. ee. 
ap Im_inc. am. ap Im_inc. am.
Qed.

Lemma Im2_ex : forall f x y z, inc z (Im2 f x y) -> exists a, exists b, inc a x & inc b y & z=f a b.
Proof.
ir. wr Im2_rw. am.
Qed.

Lemma Im2_inc : forall f x y a b, inc a x -> inc b y -> inc (f a b) (Im2 f x y).
Proof.
ir. rw Im2_rw. exists a;exists b;ee;au.
Qed.

Lemma Im2_show_inc : forall f x y z, (exists a, exists b, inc a x & inc b y & z = f a b) -> 
inc z (Im2 f x y).
Proof.
ir;rw Im2_rw;au.
Qed.


Definition product := Im2 pair.

Lemma product_pair_inc : forall a b x y, inc x a -> inc y b -> 
inc (pair x y) (product a b).
Proof.
ap Im2_inc.
Qed.

Lemma product_pair_pr : forall a b x y, inc (pair x y) (product a b) -> 
(inc x a & inc y b).
Proof.
ir. apply Im2_ex in H. nin H;nin H.
nin H;nin H0.
apply pair_eq in H1;ee;subst;am.
Qed.

Lemma product_inc : forall a b x, is_pair x -> inc (P x) a -> inc (Q x) b -> 
inc x (product a b).
Proof.
ir. nin H. clpri H0. clpri H1.
ap product_pair_inc;am.
Qed.

Lemma product_pr : forall a b x, inc x (product a b) -> 
(is_pair x & inc (P x) a & inc (Q x) b).
Proof.
ir. 
apply Im2_ex in H. nin H;nin H.
ee; subst;clpr. ap pair_is_pair. am. am.
Qed.

Lemma product_rw : forall a b x, inc x (product a b) = (is_pair x & inc (P x) a & inc (Q x) b).
Proof.
ir;ap iff_eq.
ap product_pr.
ir;ap product_inc;am.
Qed.

Lemma product_pair_rw : forall a b x y, inc (J x y) (product a b) = (inc x a & inc y b).
Proof.
ir;ap iff_eq.
ap product_pair_pr.
ir;ap product_pair_inc;am.
Qed.

Lemma product_emptyset_r : forall x, product x emptyset = emptyset.
Proof.
ir;ap empty_emptyset;ir.
apply product_pr in H;ee. edestruct emptyset_empty;am.
Qed.

Lemma product_emptyset_l : forall x,  product emptyset x = emptyset.
Proof.
ir;ap empty_emptyset;ir.
apply product_pr in H;ee. edestruct emptyset_empty;am.
Qed.




(* some basic utility stuff *)
Lemma extensionality_rw : forall x y, (forall a, inc a x  = inc a y) -> x = y.
Proof.
ir;ap extensionality;uhg;ir;first [ rw H | wr H ];am.
Qed.

Lemma inter_sub : forall x y, inc y x -> sub (inter x) y.
Proof.
ir. uhg;ir. eapply inter_all. am. am.
Qed.

Definition rep x := choose (fun y => inc y x).

Lemma rep_inc : forall x, nonempty x -> inc (rep x) x.
Proof.
ir. uf rep. ap choose_pr. am.
Qed.

Lemma inter2_l : forall a b, sub (inter2 a b) a.
Proof.
uhg;ir. apply inter2_and in H;am.
Qed.

Lemma inter2_r : forall a b, sub (inter2 a b) b.
Proof.
uhg;ir;apply inter2_and in H;am.
Qed.

Lemma inter2_comm : forall a b, inter2 a b = inter2 b a.
Proof.
ir. uf inter2. rw doubleton_comm. tv.
Qed.

Lemma union2_comm : forall a b, union2 a b = union2 b a.
Proof.
ir. uf union2. rw doubleton_comm. tv.
Qed.

Parameter nNum : E.

Axiom emptyset_N : inc emptyset nNum.

Definition oS x := tack_on x x.

Lemma oS_inc : forall x y, inc y (oS x) = (inc y x \/ y=x).
Proof.
ir. uf oS. ap tack_on_inc.
Qed.

Axiom oS_nNum : forall n, inc n nNum -> inc (oS n) nNum.

Parameter nNum_rect : forall P : E -> Type,
       P emptyset -> (forall n : E, inc n nNum -> P n -> P (oS n)) -> forall n : E, inc n nNum -> P n.

Axiom nNum_rect_0 : forall (P : E -> Type) (H0 : P emptyset) IH, nNum_rect H0 IH emptyset_N = H0.

Axiom nNum_rect_S : forall (P : E -> Type) (H0 : P emptyset) IH n (Hn : inc n nNum), nNum_rect H0 IH (oS_nNum Hn) = IH n Hn (nNum_rect H0 IH Hn).

Lemma nNum_destruct : forall x, inc x nNum -> (x = emptyset \/ exists y, inc y nNum & x = oS y).
Proof.
ap nNum_rect.
au. ir.
right. eau.
Qed.

Lemma eq_dec : forall x y:E, {x=y} + {x<>y}.
Proof.
ir. apply by_cases with (x=y);ir.
left. am. right. am.
Qed.

Lemma eq_dec_if : forall x T (a b : T), (if eq_dec x x then a else b) = a.
Proof.
ir. destruct (eq_dec x x). tv. nin n;au.
Qed.

Lemma eq_dec_if_not : forall x y, x<>y -> forall T (a b : T), (if eq_dec x y then a else b) = b.
Proof.
ir. destruct (eq_dec x y). nin e;au. nin H;au.
tv.
Qed.

Lemma P_dec : forall P, {P}+{~P}.
Proof.
ir. apply by_cases with P;ir.
left. am. right. am.
Qed.

Lemma P_dec_if : forall P : Prop, P -> forall T (a b :T), (if P_dec P then a else b) = a.
Proof.
ir. nin (P_dec P).
tv. nin b0;am.
Qed.

Lemma P_dec_if_not : forall P, ~P -> forall T (a b : T), (if P_dec P then a else b) = b.
Proof.
ir. nin (P_dec P).
nin H;am. tv.
Qed.

Lemma Im_uneq : forall f g x, (forall y, inc y x -> f y = g y) -> Im f x = Im g x.
Proof.
ir;ap extensionality;uhg;ir.
apply Im_ex in H0;nin H0;ee;subst. ap Im_show_inc;exists x0;ee. am.
ap H;am.
apply Im_ex in H0;nin H0;ee;subst. ap Im_show_inc;exists x0;ee. am.
symmetry;ap H;am.
Qed.

Ltac Im_nin H := apply Im_ex in H;nin H;nin H.

Ltac Im_incw x := ap Im_show_inc;exists x.

Ltac union_nin H := apply union_ex in H;nin H;nin H.

Lemma sub_complement : forall a b c, sub b c -> sub (complement a c) (complement a b).
Proof.
uhg;ir. apply Z_all in H0;ee;ap Z_inc.
am. uhg;ir;au.
Qed.

Lemma Im_sub : forall f a b, sub a b -> sub (Im f a) (Im f b).
Proof.
ir. uhg;ir. Im_nin H0. subst. ap Im_inc;au.
Qed.

Lemma complement_complement_id : forall s x, sub x s -> complement s (complement s x) = x.
Proof.
ir. ap extensionality;uhg;ir.
apply Z_all in H0;ee. eapply use_complement. am. am.
ap Z_inc. au. uhg;ir. apply Z_all in H1;ee. au.
Qed.

Fixpoint nNat n := match n with
  | 0 => emptyset
  | S k => oS (nNat k)
  end.

Lemma nNat_nNum : forall n, inc (nNat n) nNum.
Proof.
nin n. ap emptyset_N.
simpl. ap oS_nNum. am.
Qed.

Lemma nNum_nNat : forall n, inc n nNum -> exists n', n = nNat n'.
Proof.
ap nNum_rect;ir.
exists 0. tv.
nin H0;subst.
exists (S x). tv.
Qed.

Definition nIm (f : nat -> E) := Im (fun n => f (chooseT (fun x => n = nNat x) (nonemptyT_intro 0))) nNum.

Lemma nNum_transitiveT : forall n, inc n nNum -> forall m, inc m n -> inc m nNum.
Proof.
ap (nNum_rect (P := fun n => forall m, inc m n -> inc m nNum));ir.
apply emptyset_empty in H;nin H.
rwi oS_inc H1;nin H1.
ap H0;am.
subst;am.
Qed.

Lemma oS_N_inj : forall n, inc n nNum -> forall n', oS n = oS n' -> n=n'.

Proof.
assert (forall n, inc n nNum -> forall n', inc n' nNum -> inc n n' -> sub n n').
intros n Hn. pose (p := fun n' => inc n n' -> sub n n').
assert (forall n', inc n' nNum -> p n');try am.
ap nNum_rect;uf p;ir.
edestruct emptyset_empty;am.
ufi oS H1. rwi tack_on_inc H1.
nin H1. apply sub_trans with n0. au.
uhg;ir;uf oS;rw tack_on_inc;au.
subst. uhg;ir;uf oS;rw tack_on_inc;au.

assert (forall n, inc n nNum -> inc n n -> False).
pose (p := fun n => inc n n -> False). assert (forall n, inc n nNum -> p n);try am.
ap nNum_rect;uf p;ir. eapply emptyset_empty;am.
ufi oS H2;rwi tack_on_inc H2;nin H2. apply H in H2.
ap H1. ap H2. rw tack_on_inc;au.
ap oS_nNum. am. am.
ap H1. wr H2. rw tack_on_inc. rw H2. au.

assert (forall n, inc n nNum -> forall n', inc n' nNum -> inc n n' -> inc n' n -> False).
ir.
apply H0 with n;au.
apply H with n';au.

intros n H2 n' H4.
assert (inc n' nNum).
eapply nNum_transitiveT. ap oS_nNum. am.
rw H4;rw oS_inc;au.
assert (inc (n) (oS n')).
wr H4. uf oS;rw tack_on_inc;au.
ufi oS H5;rwi tack_on_inc H5;nin H5;au.
assert (inc n' (oS n)). rw H4.
uf oS;rw tack_on_inc;au.
ufi oS H6;rwi tack_on_inc H6;nin H6;au.
ap False_rect. eauto.
Qed.

Lemma nNat_inj : forall n n', nNat n = nNat n' -> n=n'.
Proof.
intros n. nin n;ir.
destruct n'. tv.
simpl in H. edestruct emptyset_empty.
rw H. uf oS;rw tack_on_inc;right;au.
destruct n'.
simpl in*. edestruct emptyset_empty.
wr H. uf oS;rw tack_on_inc;au.
simpl in H.
apply oS_N_inj in H. ap uneq. au.
ap nNat_nNum. 
Qed.

Lemma nIm_rw : forall f x, inc x (nIm f) = exists n, x = f n.
Proof.
ir. uf nIm. rw Im_rw. ap iff_eq;ir.
nin H;ee. subst. econstructor. reflexivity.
nin H. subst.
exists (nNat x0). ee. ap nNat_nNum.
ap uneq.
ap nNat_inj.
ap chooseT_pr. exists x0. tv.
Qed.

Lemma nIm_ex : forall f x, inc x (nIm f) -> exists n, x = f n.
Proof.
ir. wr nIm_rw. am.
Qed.

Lemma nIm_show_inc : forall f x, (exists n, x = f n) -> inc x (nIm f).
Proof.
ir;rw nIm_rw;am.
Qed.

Lemma nIm_inc : forall f n, inc (f n) (nIm f).
Proof.
ir;ap nIm_show_inc. exists n;tv.
Qed.

Lemma union_Im : forall f x y, inc y (union (Im f x)) = exists a, inc a x & inc y (f a).
Proof.
ir;ap iff_eq;ir.
union_nin H. Im_nin H;subst.
exists x1;ee;am.
nin H;ee. ap union_inc. exists (f x0);ee.
ap Im_inc. am. am.
Qed.

Lemma Im_emptyset : forall f, Im f emptyset = emptyset.
Proof.
ir. ap empty_emptyset;ir.
Im_nin H. eapply emptyset_empty;am.
Qed.

Definition nNum_rec (x0 : E) (Sf : E2) (x : E) := by_cases
(fun H : inc x nNum => nNum_rect (P := fun y => E) x0 (fun n Hn xn => Sf n xn)  H)
(fun _ : ~inc x nNum => x0).

Lemma nNum_rec_0 : forall x0 Sf, nNum_rec x0 Sf emptyset = x0.
Proof.
uf nNum_rec;ir.
erewrite by_cases_if.
rw nNum_rect_0. tv.
Qed.

Lemma nNum_rec_S : forall x0 Sf n, inc n nNum -> nNum_rec x0 Sf (oS n) = 
Sf n (nNum_rec x0 Sf n).
Proof.
ir. uf nNum_rec. erewrite by_cases_if.
rw nNum_rect_S. erewrite by_cases_if. reflexivity.
Existential 1 := H.
Qed.

Definition nNum_repeat : E1 -> E -> E -> E.
intros f n x0.
ap nNum_rec. exact x0.
intros n' xn'.
ap f. exact xn'.
exact n.
Defined.

Lemma nNum_repeat_0 : forall f x0, nNum_repeat f emptyset x0 = x0.
Proof.
ir. uf nNum_repeat. rw nNum_rec_0. tv.
Qed.

Lemma nNum_repeat_S : forall f x0 n, inc n nNum -> nNum_repeat f (oS n) x0 = 
f (nNum_repeat f n x0).
Proof.
ir. uf nNum_repeat. ap nNum_rec_S. am.
Qed.

Fixpoint nat_repeat (f : E1) (n : nat) (x0 : E) := match n with
  | 0 => x0
  | S k => f (nat_repeat f k x0)
  end.

Lemma union2_emptyset_l : forall x, union2 emptyset x = x.
Proof.
ir;ap extensionality;uhg;ir.
apply union2_or in H;nin H. edestruct emptyset_empty;am.
am.
ap union2_r. am.
Qed.

Lemma union2_emptyset_r : forall x, union2 x emptyset = x.
Proof.
ir. rw union2_comm. ap union2_emptyset_l.
Qed.

Lemma tack_on_Im : forall f x y, Im f (tack_on x y) = tack_on (Im f x) (f y).
Proof.
ir. ap extensionality_rw;ir.
rw Im_rw. rw tack_on_inc. rw Im_rw.
ap iff_eq;ir;nin H;ee;subst.
rwi tack_on_inc H;nin H;subst.
left. exists x0;ee;au.
au.
nin H;ee;subst. exists x0;ee;au.
rw tack_on_inc;au.
exists y;ee;au. rw tack_on_inc;au.
Qed.

Lemma tack_on_union : forall x y, union (tack_on x y) = union2 (union x) y.
Proof.
ir;ap extensionality;uhg;ir.
union_nin H. rwi tack_on_inc H. nin H.
ap union2_l. ap union_inc;econstructor;ee.
am. am.
subst. ap union2_r. am.
apply union2_or in H;ap union_inc.
rwi union_rw H.
nin H;try nin H;ee.
exists x0;ee. rw tack_on_inc;au. am.
exists y;ee;au. rw tack_on_inc;au.
Qed.

Lemma union2_tack_on_r : forall x y z, union2 x (tack_on y z) = tack_on (union2 x y) z.
Proof.
ir;ap extensionality_rw;ir. rw union2_rw.
rw tack_on_inc. rw tack_on_inc. rw union2_rw.
ap iff_eq;ap or_assoc.
Qed.

Lemma oS_sub : forall x, sub x (oS x).
Proof.
uhg;ir;rw oS_inc;au.
Qed.

Lemma not_empty_nonempty : forall x, x<>emptyset -> nonempty x.
Proof.
ir;ap excluded_middle;uhg;ir;ap H;ap empty_emptyset;ir.
ap H0;exists y;am.
Qed.

Lemma nonempty_not_empty : forall x, nonempty x -> x<>emptyset.
Proof.
uhg;ir. subst. nin H. eapply emptyset_empty;am.
Qed.

Notation "{ fx | x ∈ a }" := (Im (fun x => fx) a).

Lemma product_ex : forall a b x, inc x (product a b) -> exists xa, exists xb, x = J xa xb & inc xa a & inc xb b.
Proof.
ir. apply product_pr in H. ee. nin H.
clpri H0;clpri H1. exists a0;exists b0;ee;au.
Qed.

Ltac product_nin H := apply product_ex in H;nin H;nin H;ee.

Ltac emptyset_nin H := destruct (emptyset_empty H).

Ltac emptyset_auto := match goal with 
  | id1:(inc _ emptyset) |- _ => emptyset_nin id1
  end.

End Axioms. Export Axioms.

