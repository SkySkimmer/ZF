
Set Implicit Arguments.
Unset Strict Implicit.

Require Export functions.

Module Family_relation.
Export Map. Export Function.

Section Var.

Variables (I : E) (r : E2P) (a : E).

Definition innerRel x y := is_map I a x & is_map I a y & 
(forall z, inc z I -> r (ev x z) (ev y z)).

Lemma innerRel_refl : reflexiveT r a -> reflexiveT innerRel (map_set I a).
Proof.
ir;uhg;ir.
rwi map_set_rw H0. uhg;ee;au. ir.
ap H;eapply trans_of_map;am.
Qed.

Lemma innerRel_sym : symmetricT r a -> symmetricT innerRel (map_set I a).
Proof.
ir;uhg;ir. 
rwi map_set_rw H0;rwi map_set_rw H1.
uh H2;ee.
uhg;ee;au. ir. ap H;try (eapply trans_of_map;am).
ap H4. am.
Qed.

Lemma innerRel_antisym : antisymmetricT r a -> antisymmetricT innerRel (map_set I a).
Proof.
uhg;ir. uh H2;uh H3;ee.
eapply map_extensionality.
am. am. ir.
ap H. eapply trans_of_map;am. eapply trans_of_map;am.
ap H7;am. ap H5;am.
Qed.

Lemma innerRel_trans : transitiveT r a -> transitiveT innerRel (map_set I a).
Proof.
uhg;ir.
clear H0;clear H1;clear H3.
uh H2;uh H4;ee.
uhg;ee;au.
ir. apply H with (ev y z0);au;eapply trans_of_map;am.
Qed.

(*NB : not total*)

Lemma innerRel_order : is_order r a -> is_order innerRel (map_set I a).
Proof.
uhg;ir;ee.
ap innerRel_refl. am.
ap innerRel_antisym. am.
ap innerRel_trans. am.
Qed.

Lemma innerRel_equiv : is_equivalence r a -> is_equivalence innerRel (map_set I a).
Proof.
ir. uhg;ee. ap innerRel_refl. am.
ap innerRel_sym;am.
ap innerRel_trans;am.
Qed.

End Var.

End Family_relation.

Module Quotient.
Export Map. Export Function.

Section Var.

Variables (r : E2P) (a : E).

Hypothesis (Heq : is_equivalence r a).

Definition class_of x := Z a (r x).

Inductive is_class : EP :=
  | class_of_class : forall x, inc x a -> is_class (class_of x)
.

Lemma related_classes_eq : forall x, inc x a -> forall y, inc y a -> 
r x y -> class_of x = class_of y.
Proof.
ir;ap extensionality_rw;intros b.
uf class_of. rw Z_rw. rw Z_rw. ap iff_eq;ir;ee;au.
cp (and_Q Heq). ee. apply H5 with x;try am.
ap H4;am.
cp (and_Q Heq). ee. apply H5 with y;try am.
Qed.

Lemma class_of_origin : forall x, inc x a -> inc x (class_of x).
Proof.
ir. ap Z_inc;au. ap (and_P Heq). am.
Qed.

Lemma class_of_eq_related : forall x, inc x a -> forall y, inc y a -> 
class_of x = class_of y -> r x y.
Proof.
ir. assert (inc y (class_of y)). ap class_of_origin;am.
wri H1 H2. apply Z_pr in H2. am.
Qed.

Lemma is_class_rw : forall x, is_class x = exists y, inc y a & x = class_of y.
Proof.
ir;ap iff_eq;ir.
nin H. exists x;ee;au.
nin H;ee;subst;constructor;am.
Qed.

Lemma class_sub : forall x, is_class x -> sub x a.
Proof.
ir. nin H. ap Z_sub.
Qed.

Lemma class_nonempty : forall x, is_class x -> nonempty x.
Proof.
ir. nin H. exists x. ap class_of_origin. am.
Qed.

Lemma class_rep_inc : forall x, is_class x -> inc (rep x) x.
Proof.
ir. ap rep_inc. ap class_nonempty. am.
Qed.

Lemma class_eq_class_of : forall x, is_class x -> forall y, inc y x -> 
class_of y = x.
Proof.
ir. nin H.
apply Z_all in H0;ee.
ap related_classes_eq;try am. ap Heq;am.
Qed.

Lemma intersecting_classes_eq : forall x, is_class x -> forall y, is_class y -> 
inter2 x y <> emptyset -> x=y.
Proof.
ir. apply not_empty_nonempty in H1. nin H1.
apply inter2_and in H1. ee.
apply class_eq_class_of in H1;au.
apply class_eq_class_of in H2;au.
subst;tv.
Qed.

Lemma rep_related : forall x, inc x a -> r x (rep (class_of x)).
Proof.
ir. eapply Z_pr. ap class_rep_inc. ap class_of_class. am.
Qed.

Definition quotient := Z (powerset a) (is_class).

Lemma class_in_quotient : forall x, is_class x -> inc x quotient.
Proof.
ir;ap Z_inc;au. ap powerset_inc. ap class_sub. am.
Qed.

Lemma class_of_in_quotient : forall x, inc x a -> inc (class_of x) quotient.
Proof.
ir;ap class_in_quotient. constructor. am.
Qed.

Definition class_in q x := unique_choose (fun y => inc x y & inc y q).

Lemma class_in_pr : forall x, inc x a -> (inc x (class_in quotient x) & inc (class_in quotient x) quotient).
Proof.
ir. uf class_in. ap unique_choose_pr.
exists (class_of x). ee.
ap class_of_origin;am.
ap class_of_in_quotient. am.
uhg;ir. ee.
apply Z_pr in H3;apply Z_pr in H2.
ap intersecting_classes_eq. am. am.
ap nonempty_not_empty. exists x;ap inter2_inc;am.
Qed.

Lemma class_in_is_class : forall x, inc x a -> is_class (class_in quotient x).
Proof.
ir. apply class_in_pr in H;ee. apply Z_pr in H0.
am.
Qed.

Lemma class_of_class_in : forall x, inc x a -> class_of x = class_in quotient x.
Proof.
ir. cp (class_in_pr H).
ee. apply Z_pr in H1.
ap intersecting_classes_eq.
ap class_of_class;am.
am.
ap nonempty_not_empty.
exists x;ap inter2_inc. ap class_of_origin;am.
am.
Qed.

Lemma class_of_rep : forall x, is_class x -> x = class_of (rep x).
Proof.
ir. symmetry. ap class_eq_class_of.
am. ap class_rep_inc. am.
Qed.

Lemma class_rep_in : forall x, is_class x -> inc (rep x) a.
Proof.
ir. eapply class_sub. am. ap class_rep_inc. am.
Qed.

End Var.

Section Passes.

Variables (r : E2P) (a : E).

Hypothesis (Heq : is_equivalence r a).

Variables (r' : E2P) (a' : E).

Hypothesis (Heq' : is_equivalence r' a').

Variable (f : E).

Hypothesis (Hf : is_morphism r a r' a' f).
(*morphism : map + compatible*)

Definition quofun := L (quotient r a) (fun c => class_in (quotient r' a') (ev f (rep c))).

Lemma quofun_map : is_map (quotient r a) (quotient r' a') quofun.
Proof.
uf quofun. ap map_of_trans.
uhg;ir. ap class_in_pr. am. eapply trans_of_map. am.
eapply class_sub. apply Z_pr in H. am.
eapply class_rep_inc. ap Heq. apply Z_pr in H;am.
Qed.

Lemma quofun_passes : forall x, inc x a -> 
ev quofun (class_of r a x) = class_of r' a' (ev f x).
Proof.
ir.
uf quofun. rw create_ev. wr class_of_class_in.
ap related_classes_eq. am.
eapply trans_of_map. am.
eapply class_rep_in. am. ap class_of_class;am.

eapply trans_of_map. am. am.
ap Hf. 
eapply class_rep_in. am. ap class_of_class;am.
am.
eapply class_of_eq_related.
am. eapply class_rep_in. am. ap class_of_class;am.
am.
symmetry. ap class_of_rep.
am. ap class_of_class;am.
am.
eapply trans_of_map. am.
eapply class_rep_in. am. ap class_of_class;am.
ap class_of_in_quotient. am.
Qed.

End Passes.

Section Passes2.

Import Family_relation.

Variables (r : E2P) (a : E).

Hypothesis (Heq : is_equivalence r a).

Variables (r' : E2P) (a' : E).

Hypothesis (Heq' : is_equivalence r' a').

Variable (f : E2).

Hypothesis (Hfi : forall x, inc x a -> forall y, inc y a -> inc (f x y) a').
Hypothesis (Hfc : forall x, inc x a -> forall y, inc y a -> r x y -> 
forall x', inc x' a -> forall y', inc y' a -> r x' y' -> 
r' (f x x') (f y y')).

Notation I := (doubleton emptyset (oS emptyset)).
Notation g := (L (map_set I a) 
(fun v => f (ev v emptyset) (ev v (oS emptyset)))).

Definition opfun : E.
ap quofun. ap innerRel.
exact I. exact r. exact a.
exact (map_set I a).
exact r'. exact a'.
exact g.
Defined.

Lemma opfun_passes_aux : forall x, inc x (map_set I a) -> 
ev opfun (class_of (innerRel I r a) (map_set I a) x) = class_of r' a' (ev g x).
Proof.
ir. uf opfun. etransitivity. eapply quofun_passes.
ap innerRel_equiv. am. am.
uhg;ee.
ap map_of_trans.
uhg;ir.
rwi map_set_rw H0. rwi map_set_rw H. 
ap Hfi;
eapply trans_of_map;try am.
ap doubleton_l. ap doubleton_r.
ir. uh H2;ee.
rw create_ev;try am.
rw create_ev;try am.
rwi map_set_rw H;rwi map_set_rw H0;rwi map_set_rw H1.
ap Hfc;try ( eapply trans_of_map;try am).
ap doubleton_l. ap doubleton_l. ap H4.
ap doubleton_l. ap doubleton_r. ap doubleton_r. ap H4.
ap doubleton_r. am.
tv.
Qed.

(*
where x, y are classes in r, a
then L I (fun z => if z=emptyset then rep x else rep y) is in map_set I a
*)
Definition quotient_op (x y : E) := ev opfun (class_of (innerRel I r a) (map_set I a) (L I (fun z => 
if eq_dec emptyset z then rep x else rep y))).

Lemma quotient_op_passes : forall x, inc x a -> forall y, inc y a -> 
quotient_op (class_of r a x) (class_of r a y) = class_of r' a' (f x y).
Proof.
ir.
uf quotient_op.
assert (inc (L I
        (fun z : E =>
         if eq_dec ∅ z then rep (class_of r a x) else rep (class_of r a y))) (map_set I a)).
rw map_set_rw. ap map_of_trans.
uhg;ir. apply doubleton_or in H1. nin H1;subst.
rw eq_dec_if. eapply class_rep_in. am. ap class_of_class;am.
rw eq_dec_if_not. eapply class_rep_in. am. ap class_of_class;am.
uhg;ir;apply emptyset_empty with emptyset;eapply eq_ind;try (symmetry;am).
rw oS_inc;au. 
rw opfun_passes_aux;try am.
rw create_ev. Focus 2.
am.
rw create_ev. rw create_ev.
Focus 2. ap doubleton_r. Focus 2. ap doubleton_l.
rw eq_dec_if. rw eq_dec_if_not.
ap related_classes_eq. am.
ap Hfi;eapply class_rep_in;try am;ap class_of_class;am.
ap Hfi;am.
assert (forall z, inc z a -> inc (rep (class_of r a z)) a).
ir. eapply class_rep_in;try am;ap class_of_class;am.
ap Hfc;au.
ap Heq;au. ap rep_related. am. am.
ap Heq;au. ap rep_related. am. am.
uhg;ir;apply emptyset_empty with emptyset;eapply eq_ind;try symmetry;try am.
rw oS_inc;au.
Qed.


End Passes2.

End Quotient.

