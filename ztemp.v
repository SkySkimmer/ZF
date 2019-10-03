
Set Implicit Arguments.
Unset Strict Implicit.

Require Export nnum_base.
Require Import aac.
Require Export quotient.

Module ZTemp.
Import nNum_ring.
Export Quotient.
Import Ordered_lci.
Export Pow.

Section NotaSec.

Definition zEquiv x y := (nPlus (P x) (Q y) = nPlus (P y) (Q x)).

Definition zNum := quotient zEquiv (product nNum nNum).

Notation "[ x ]" := (class_of zEquiv (product nNum nNum) x).

Definition z0 := [J n0 n0].

Definition z1 := [J n1 n0].

Lemma zEquiv_equiv : is_equivalence zEquiv (product nNum nNum).
Proof.
uhg;ee;uhg;ir.
product_nin H. ee. subst.
uhg. clpr. tv.
product_nin H;product_nin H0;ee;subst.
uh H1;uhg. clpri H1;clpr. au.
product_nin H;product_nin H0;product_nin H2;ee;subst.
uh H3;uh H1;uhg.
clpri H1;clpri H3. clpr.
apply nPlus_reg_l with x3;nSolveS.
rw nPlus_assoc. rw (nPlus_comm x3). rw H1.
wr nPlus_assoc. rw (nPlus_comm x1). rw nPlus_assoc.
rw H3. AAC_all.aac_solve_all (nPlus_assoc) (nPlus_comm).
Qed.

Lemma zNum_inc_rw : forall x, inc x zNum = (exists a, exists b, inc a nNum & inc b nNum & x = [J a b]).
Proof.
ir;ap iff_eq;ir.
apply Z_pr in H. nin H.
product_nin H. exists x0;exists x1;ee;au. ap uneq;am.
nin H;nin H;ee;subst.
ap class_in_quotient. ap class_of_class. ap product_pair_inc;am.
Qed.

Lemma zNum_inc : forall a, inc a nNum -> forall b, inc b nNum -> 
inc [J a b] zNum.
Proof.
ir. rw zNum_inc_rw. exists a;exists b;ee;au.
Qed.

Lemma z0_inc : inc z0 zNum.
Proof.
ap zNum_inc;nSolveS.
Qed.

Lemma z1_inc : inc z1 zNum.
Proof.
ap zNum_inc;nSolveS.
Qed.

Definition zPlus := quotient_op zEquiv (product nNum nNum) zEquiv (product nNum nNum) (fun x y => J (nPlus (P x) (P y)) (nPlus (Q x) (Q y))).

Lemma zPlus_passes_p : forall x, inc x (product nNum nNum) -> forall y, inc y (product nNum nNum) -> 
zPlus [x] [y] = [J (nPlus (P x) (P y)) (nPlus (Q x) (Q y))].
Proof.
uf zPlus.
ap quotient_op_passes. 

ap zEquiv_equiv. ap zEquiv_equiv.
ir. product_nin H;product_nin H0.
ee;subst. clpr. ap product_pair_inc;nSolveS.
ir. product_nin H;product_nin H0;product_nin H2;product_nin H3.
ee;subst. clpr. uh H4;uh H1.
clpri H4;clpri H1.
uhg. clpr.
transitivity (nPlus (nPlus x0 x3) (nPlus x4 x7)).
AAC_all.aac_solve_all nPlus_assoc nPlus_comm.
rw H1;rw H4. AAC_all.aac_solve_all nPlus_assoc nPlus_comm.
Qed.

Lemma zPlus_passes : forall a, inc a nNum -> forall b, inc b nNum -> 
forall a', inc a' nNum -> forall b', inc b' nNum -> 
zPlus [J a b] [J a' b'] = [J (nPlus a a') (nPlus b b')].
Proof.
ir. rw zPlus_passes_p. clpr. tv.
apply product_pair_inc;am. apply product_pair_inc;am.
Qed.

Lemma zPlus_lci : is_lci zPlus zNum.
Proof.
uhg;ir. rwi zNum_inc_rw H;rwi zNum_inc_rw H0.
nin H;nin H;nin H0;nin H0;ee;subst.
rw zPlus_passes;au. ap zNum_inc;nSolveS.
Qed.

Lemma zPlus_comm : commutative zPlus zNum.
Proof.
uhg;ir. rwi zNum_inc_rw H;rwi zNum_inc_rw H0.
nin H;nin H;nin H0;nin H0;ee;subst.
rw zPlus_passes;au. rw zPlus_passes;au.
rw nPlus_comm. ap uneq. ap uneq. ap nPlus_comm.
Qed.

Lemma zPlus_assoc : associative zPlus zNum.
Proof.
uhg;ir. rwi zNum_inc_rw H;rwi zNum_inc_rw H0;rwi zNum_inc_rw H1.
nin H;nin H;nin H0;nin H0;nin H1;nin H1;ee;subst.
rw zPlus_passes;au. rw zPlus_passes;nSolveS.
rw zPlus_passes;nSolveS. rw zPlus_passes;nSolveS.
rw nPlus_assoc. rw nPlus_assoc. tv.
Qed.

Lemma z0_eq : forall a, inc a nNum -> [J a a] = z0.
Proof.
ir. ap related_classes_eq.
ap zEquiv_equiv.
ap product_pair_inc;au.
ap product_pair_inc;nSolveS.
uhg. clpr. ap nPlus_comm.
Qed.

Lemma zNum_eq : forall a, inc a nNum -> forall b, inc b nNum -> 
forall c, inc c nNum -> forall d, inc d nNum -> 
([J a b] = [J c d]) = (zEquiv (J a b) (J c d)).
Proof.
ir. ap iff_eq;ir.
eapply class_of_eq_related.
ap zEquiv_equiv. ap product_pair_inc;am.
ap product_pair_inc;am. am.
ap related_classes_eq. ap zEquiv_equiv.
apply product_pair_inc;am. apply product_pair_inc;am.
am.
Qed.

Lemma zPlus_z0_l : forall x, inc x zNum -> zPlus z0 x = x.
Proof.
ir. rwi zNum_inc_rw H. nin H;nin H;ee;subst.
uf z0. rw zPlus_passes;nSolveS.
rw nPlus_0_l. rw nPlus_0_l. tv. am. am.
Qed.

Lemma zPlus_z0_r : forall x, inc x zNum -> zPlus x z0 = x.
Proof.
ir. rw zPlus_comm. ap zPlus_z0_l. am.
am. ap z0_inc.
Qed.

Lemma zPlus_z0_neutre : is_neutre zPlus zNum z0.
Proof.
uhg;ee. ap z0_inc. ap zPlus_z0_r. ap zPlus_z0_l.
Qed.

Lemma zPlus_monoid : is_monoid zPlus zNum z0.
Proof.
uhg;ee.
ap zPlus_lci. ap zPlus_z0_neutre. ap zPlus_assoc.
Qed.

Lemma zPlus_inversible : forall x, inc x zNum -> inversible zPlus zNum z0 x.
Proof.
ir. rwi zNum_inc_rw H;nin H;nin H;ee;subst.
exists [J x1 x0]. uhg;ee.
ap zNum_inc;am. ap zNum_inc;am.
rw zPlus_passes;au. rw nPlus_comm.
ap z0_eq. nSolveS.
rw zPlus_passes;au. rw nPlus_comm.
ap z0_eq. nSolveS.
Qed.

Lemma zPlus_group : is_group zPlus zNum z0.
Proof.
uhg;ee;try ap zPlus_monoid.
ap zPlus_inversible.
Qed.

Definition zOpp := Lci.inverse_of zPlus zNum z0.

Lemma zOpp_inverse : forall x, inc x zNum -> Lci.are_inverse zPlus zNum z0 x (zOpp x).
Proof.
ir. ap group_inverse_of. ap zPlus_group. am.
Qed.

Lemma zOpp_inc : forall x, inc x zNum -> inc (zOpp x) zNum.
Proof.
ir;ap zOpp_inverse;am.
Qed.

Lemma zOpp_rw : forall a, inc a nNum -> forall b, inc b nNum -> 
zOpp [J a b] = [J b a].
Proof.
ir. eapply Lci.inverse_unicity.
ap zPlus_monoid.
ap zOpp_inverse. ap zNum_inc;am.
uhg;ee;try (ap zNum_inc;am).
rw zPlus_passes;au. rw nPlus_comm.
ap z0_eq. nSolveS.
rw zPlus_passes;au. rw nPlus_comm.
ap z0_eq. nSolveS.
Qed.

Lemma zOpp_l : forall x, inc x zNum -> zPlus (zOpp x) x = z0.
Proof.
ir. ap zOpp_inverse. am.
Qed.

Lemma zOpp_r : forall x, inc x zNum -> zPlus x (zOpp x)  = z0.
Proof.
ir. ap zOpp_inverse. am.
Qed.

Lemma z0_z1_neq : z0<>z1.
Proof.
uhg;ir.
ufi z0 H;ufi z1 H.
apply class_of_eq_related in H.
uh H;clpri H.
rwi nPlus_0 H;nSolveS.
rwi nPlus_0 H;nSolveS.
eapply ordinal_inc_neq. ap ordinal_S. ap emptyset_ordinal.
Focus 2. ap H.
rw oS_inc;au.
ap zEquiv_equiv.
ap product_pair_inc;nSolveS. ap product_pair_inc;nSolveS.
Qed.

(*(a-b)*(c-d) = (ac+bd) - (b c + a d)*)
Definition zMult0 :=  (fun x y => let a := P x in let b := Q x in let c := P y in let d := Q y in 
J (nPlus (nMult a c) (nMult b d)) (nPlus (nMult b c) (nMult a d))).

Definition zMult := quotient_op zEquiv (product nNum nNum) 
zEquiv (product nNum nNum) zMult0.

Lemma zEquiv_zMult0_compat : Ordered_lci.is_compatible zEquiv zMult0 (product nNum nNum).
Proof.
ap Ordered_lci.invariant_transitive_compat.
ap zEquiv_equiv. uhg;ir.
product_nin H;product_nin H0;uf zMult0. subst;clpr.
ap product_pair_inc;nSolveS.

uhg. dj.
uhg;ir.
product_nin H;product_nin H0;product_nin H1. subst.
uh H2;clpri H2.
uhg;uf zMult0;clpr.
transitivity (nPlus (nPlus (nMult x2 x0) (nMult x5 x0)) (nPlus (nMult x3 x1) (nMult x4 x1))).
AAC_all.aac_solve_all nPlus_assoc nPlus_comm.
wr nMult_distrib_r. rw H2. wr nMult_distrib_r. 
rw nMult_distrib_r. rw (nPlus_comm x3). wr H2.
rw nMult_distrib_r. 
AAC_all.aac_solve_all nPlus_assoc nPlus_comm.
uh H. uhg.
assert (forall x y, zMult0 x y = zMult0 y x).
ir;uf zMult0. rw nMult_comm. rw (nMult_comm (Q x)).
ap uneq. rw nPlus_comm. rw nMult_comm. ap uneq.
ap nMult_comm.
ir. rw H0. rw (H0 x). ap H. am. am. am. am.
Qed.

Lemma zMult_passes_p : forall x, inc x (product nNum nNum) -> forall y, inc y (product nNum nNum) -> 
zMult [x] [y] = [J (nPlus (nMult (P x) (P y)) (nMult (Q x) (Q y))) (nPlus (nMult (Q x) (P y)) (nMult (P x) (Q y)))].
Proof.
ir. uf zMult.
rw quotient_op_passes. tv.
ap zEquiv_equiv. ap zEquiv_equiv.
clear H;clear H0;clear x;clear y.
ir. uf zMult0.
product_nin H. product_nin H0. ee;subst.
clpr. ap product_pair_inc;nSolveS.

clear H;clear H0;clear x;clear y.

ir. ap zEquiv_zMult0_compat;am.
am. am.
Qed.

Lemma zMult_passes : forall a, inc a nNum -> forall b, inc b nNum -> 
forall c, inc c nNum -> forall d, inc d nNum -> 
zMult [J a b] [J c d] = [J (nPlus (nMult a c) (nMult b d)) (nPlus (nMult b c) (nMult a d))].
Proof.
ir. rw zMult_passes_p. clpr. tv.
ap product_pair_inc;am. ap product_pair_inc;am.
Qed.
(*beautiful*)

Lemma zMult_lci : is_lci zMult zNum.
Proof.
uhg;ir. rwi zNum_inc_rw H;rwi zNum_inc_rw H0.
nin H;nin H;nin H0;nin H0;ee;subst.
rw zMult_passes;au. ap zNum_inc;nSolveS.
Qed.

Lemma zMult_comm : commutative zMult zNum.
Proof.
uhg;ir. rwi zNum_inc_rw H;rwi zNum_inc_rw H0.
nin H;nin H;nin H0;nin H0;ee;subst.
rw zMult_passes;au. rw zMult_passes;au.
ap uneq. rw nMult_comm. rw (nMult_comm x1). ap uneq.
rw nPlus_comm. rw nMult_comm. ap uneq.
ap nMult_comm.
Qed.

Lemma zMult_assoc : associative zMult zNum.
Proof.
uhg;ir. rwi zNum_inc_rw H;rwi zNum_inc_rw H0;rwi zNum_inc_rw H1.
nin H;nin H;nin H0;nin H0; nin H1;nin H1;ee;subst.
rw zMult_passes;au. rw zMult_passes;nSolveS.
rw zMult_passes;au. rw zMult_passes;nSolveS.
ap uneq.
ap uneq2.
rw nMult_distrib_r. rw nMult_distrib_r.
rw nMult_distrib_l. rw nMult_distrib_l.
repeat wr nMult_assoc.
AAC_all.aac_solve_all nPlus_assoc nPlus_comm.
rw nMult_distrib_r. rw nMult_distrib_r.
rw nMult_distrib_l. rw nMult_distrib_l.
repeat wr nMult_assoc.
AAC_all.aac_solve_all nPlus_assoc nPlus_comm.
Qed.

Lemma zMult_0_l : forall x, inc x zNum -> zMult z0 x = z0.
Proof.
ir. rwi zNum_inc_rw H. nin H;nin H;ee;subst.
uf z0. rw zMult_passes;nSolveS.
rw nMult_0_l. rw nMult_0_l. rw nPlus_0;nSolveS.
Qed.

Lemma zMult_0_r : forall x, inc x zNum -> zMult x z0 = z0.
Proof.
ir. rw zMult_comm;au. ap zMult_0_l;au.
ap z0_inc.
Qed.

Lemma zMult_1_l : forall x, inc x zNum -> zMult z1 x = x.
Proof.
ir. uf z1;rwi zNum_inc_rw H;nin H;nin H;ee;subst.
rw zMult_passes;nSolveS.
rw nMult_1_l;nSolveS. rw nMult_0_l. rw nMult_0_l.
rw nMult_1_l;nSolveS. rw nPlus_0;nSolveS. rw nPlus_0_l;nSolveS.
Qed.

Lemma zMult_1_r : forall x, inc x zNum -> zMult x z1 = x.
Proof.
ir. rw zMult_comm;au. ap zMult_1_l;au.
ap z1_inc.
Qed.

Lemma zMult_1_neutre : is_neutre zMult zNum z1.
Proof.
uhg;ee. ap z1_inc. ap zMult_1_r. ap zMult_1_l.
Qed.

Lemma zMult_monoid : is_monoid zMult zNum z1.
Proof.
uhg;ee. ap zMult_lci. ap zMult_1_neutre.
ap zMult_assoc.
Qed.

Lemma zNum_pos_neg : forall x, inc x zNum = 
((exists a, inc a nNum & x = [J a emptyset])\/(exists b, inc b nNum & x = [J emptyset b])).
Proof.
ir;ap iff_eq;ir.
rwi zNum_inc_rw H;nin H;nin H;ee;subst.
destruct nLeq_total with x0 x1;try am;rwi nLeq_rw H1;au;nin H1;ee;subst.
right. exists x;ee. am.
ap related_classes_eq. ap zEquiv_equiv.
ap product_pair_inc;nSolveS.
ap product_pair_inc;nSolveS.
uhg;clpr.
rw nPlus_0_l;nSolveS.
left. exists x;ee. am.
ap related_classes_eq. ap zEquiv_equiv.
ap product_pair_inc;nSolveS.
ap product_pair_inc;nSolveS.
uhg;clpr.
rw nPlus_0;nSolveS. ap nPlus_comm.
nin H;nin H;ee;subst;ap zNum_inc;nSolveS.
Qed.

Lemma z0_eq_pr : forall a, inc a nNum -> forall b, inc b nNum -> 
[J a b] = z0 -> a=b.
Proof.
ir. apply class_of_eq_related in H1.
uh H1;clpri H1. rwi nPlus_0 H1;au. rw H1.
ap nPlus_0_l;au.
ap zEquiv_equiv.
ap product_pair_inc;am.
ap product_pair_inc;ap n0_inc.
Qed.

Lemma zMult_integral : is_integral zMult zNum z0.
Proof.
uhg;ir.
rwi zNum_pos_neg H;rwi zNum_pos_neg H0.
nin H;nin H0;nin H;nin H0;ee;subst;
rwi zMult_passes H1;nSolveS;repeat rwi nMult_0 H1;repeat rwi nMult_0_l H1.
rwi nPlus_0 H1;nSolveS. rwi nPlus_0 H1;nSolveS. 
apply z0_eq_pr in H1;nSolveS.
apply nMult_integral_all in H1. nin H1;subst.
left. tv.
right. tv.
rwi nPlus_0 H1;nSolveS. rwi nPlus_0_l H1;nSolveS. 
apply z0_eq_pr in H1;nSolveS. symmetry in H1.
apply nMult_integral_all in H1. nin H1;subst.
left. tv.
right. tv.
rwi nPlus_0 H1;nSolveS. rwi nPlus_0 H1;nSolveS. 
apply z0_eq_pr in H1;nSolveS. symmetry in H1.
apply nMult_integral_all in H1. nin H1;subst.
left. tv.
right. tv.
rwi nPlus_0 H1;nSolveS. rwi nPlus_0_l H1;nSolveS. 
apply z0_eq_pr in H1;nSolveS.
apply nMult_integral_all in H1. nin H1;subst.
left. tv.
right. tv.
Qed.

Lemma zPlus_regular : is_regular zPlus zNum.
Proof.
ap (group_is_regular zPlus_group).
Qed.

Lemma zPlus_reg_l : is_reg_l zPlus zNum.
Proof.
ap zPlus_regular.
Qed.

Lemma zPlus_reg_r : is_reg_r zPlus zNum.
Proof.
ap zPlus_regular.
Qed.

Lemma zMult_distrib_l : distrib_l zPlus zMult zNum.
Proof.
uhg. ir.
rwi zNum_inc_rw H;rwi zNum_inc_rw H0;rwi zNum_inc_rw H1.
nin H;nin H;nin H0;nin H0;nin H1;nin H1. ee;subst.
rw zPlus_passes;nSolveS. rw zMult_passes;nSolveS.
rw zMult_passes;nSolveS. rw zMult_passes;nSolveS.
rw zPlus_passes;nSolveS.
rw nMult_distrib_l. rw nMult_distrib_l.
rw nMult_distrib_l.  rw nMult_distrib_l. 
ap uneq. ap uneq2;AAC_all.aac_solve_all nPlus_assoc nPlus_comm.
Qed.

Lemma zMult_distrib_r : distrib_r zPlus zMult zNum.
Proof.
uhg;ir. rw zMult_comm.
rw zMult_distrib_l;try am.
ap uneq2;ap zMult_comm;am.
ap zPlus_lci;am.
am.
Qed.

Lemma zMult_distributes : distributes zPlus zMult zNum.
Proof.
uhg;ee. ap zMult_distrib_l. ap zMult_distrib_r.
Qed.

Lemma zNum_ring : is_ring zPlus zMult zNum z0 z1.
Proof.
uhg;ee. ap zPlus_group. ap zPlus_comm. ap zMult_monoid.
 ap zMult_distributes.
Qed.

Definition zMult_reg_l := integral_quasiregular_left zNum_ring zMult_integral.
Definition zMult_reg_r := integral_quasiregular_right zNum_ring zMult_integral.

(*(a-b) <= (c-d) iff a+d <= c+b*)
Inductive zLeq : E2P := 
  | zLeq_in : forall a, inc a nNum -> forall b, inc b nNum -> forall c, inc c nNum -> forall d, inc d nNum -> 
nLeq (nPlus a d) (nPlus c b) -> zLeq [J a b] [J c d].

Lemma zLeq_rw : forall a, inc a nNum -> forall b, inc b nNum -> forall c, inc c nNum -> forall d, inc d nNum -> 
zLeq [J a b] [J c d] = nLeq (nPlus a d) (nPlus c b).
Proof.
ir. ap iff_eq;ir.
inversion H3.
apply class_of_eq_related in H4;try ap zEquiv_equiv;try ap product_pair_inc;nSolveS.
apply class_of_eq_related in H5;try ap zEquiv_equiv;try ap product_pair_inc;nSolveS.
uh H4;uh H5;clpri H4;clpri H5.
rwi nLeq_rw H10;nSolveS.
nin H10;ee.
apply nLeq_nPlus_reg_l with (nPlus b0 c0);nSolveS.
replace (nPlus (nPlus b0 c0) (nPlus a d)) with (nPlus (nPlus a0 b) (nPlus c d0)).
Focus 2. rw H4. wr H5. AAC_all.aac_solve_all nPlus_assoc nPlus_comm.
rwi nPlus_comm H11. rw H11.
rw nLeq_rw;nSolveS.
exists x;ee. am.
AAC_all.aac_solve_all nPlus_assoc nPlus_comm.
constructor;am.
Qed.

Lemma zLeq_inc : forall x y, zLeq x y -> (inc x zNum & inc y zNum).
Proof.
ir. nin H. ee;ap zNum_inc;am.
Qed.

Lemma zLeq_refl : reflexiveT zLeq zNum.
Proof.
uhg;ir. rwi zNum_inc_rw H;nin H;nin H;ee;subst.
constructor;try am. ap sub_refl.
Qed.

Lemma zLeq_antisym : antisymmetricT zLeq zNum.
Proof.
uhg;ir. nin H1.
rwi zLeq_rw H2;nSolveS.
cp (extensionality H2 H6).
ap related_classes_eq. ap zEquiv_equiv.
ap product_pair_inc;am. ap product_pair_inc;am.
uhg. clpr. au.
Qed.

Lemma zLeq_zMult_preserves : Ordered_ring.order_preserves zLeq zMult zNum z0.
Proof.
uhg. ir.
rwi zNum_inc_rw H. rwi zNum_inc_rw H1.
nin H;nin H;nin H1;nin H1;ee;subst.
ufi z0 H2. ufi z0 H0.
rwi zLeq_rw H2;nSolveS. rwi zLeq_rw H0;nSolveS.
rwi nPlus_0 H2;nSolveS. rwi nPlus_0_l H2;nSolveS.
rwi nPlus_0 H0;nSolveS. rwi nPlus_0_l H0;nSolveS.
rw zMult_passes;nSolveS.
uf z0. constructor;nSolveS.
rw nPlus_0;nSolveS. rw nPlus_0_l;nSolveS.
rwi nLeq_rw H2;nSolveS.
rwi nLeq_rw H0;nSolveS.
nin H2;nin H0;ee;subst.
rw nMult_distrib_r. rw nMult_distrib_r.
rw nMult_distrib_l. rw nMult_distrib_l.
rw nLeq_rw;nSolveS.
exists (nMult x4 x). ee. nSolveS.
AAC_all.aac_solve_all nPlus_assoc nPlus_comm.
Qed.

Lemma zPos_rw : forall x, zLeq z0 x = exists a, inc a nNum & x = [J a emptyset].
Proof.
ir. ap iff_eq;ir.
cp (zLeq_inc H). ee.
rwi zNum_inc_rw H1. nin H1;nin H1;ee;subst.
ufi z0 H. rwi zLeq_rw H;nSolveS.
rwi nPlus_0 H;nSolveS. rwi nPlus_0_l H;nSolveS.
rwi nLeq_rw H;nSolveS. nin H;ee;subst.
exists x;ee. am.
ap related_classes_eq;try ap product_pair_inc;nSolveS.
ap zEquiv_equiv. uhg;clpr.
rw nPlus_0;nSolveS. ap nPlus_comm.
nin H;ee;subst. uf z0. constructor;nSolveS.
rw nPlus_0;nSolveS.
Qed.

Lemma zLeq_total : is_total zLeq zNum.
Proof.
uhg;ir. rwi zNum_inc_rw H;rwi zNum_inc_rw H0.
nin H;nin H;nin H0;nin H0;ee;subst.
rw zLeq_rw;nSolveS. rw zLeq_rw;nSolveS.
ap nLeq_total;nSolveS.
Qed.

Lemma zNeg_rw : forall x, zLeq x z0 = exists b, inc b nNum & x = [J n0 b].
Proof.
ir. ap iff_eq;ir.
cp (zLeq_inc H). ee.
rwi zNum_inc_rw H0. nin H0;nin H0;ee;subst.
ufi z0 H. rwi zLeq_rw H;nSolveS.
rwi nPlus_0 H;nSolveS. rwi nPlus_0_l H;nSolveS.
rwi nLeq_rw H;nSolveS. nin H;ee;subst.
exists x;ee. am.
ap related_classes_eq;try ap product_pair_inc;nSolveS.
ap zEquiv_equiv. uhg;clpr.
rw nPlus_0_l;nSolveS.
nin H;ee;subst. uf z0. constructor;nSolveS.
rw nPlus_0;nSolveS.
Qed.

Lemma zLeq_ex_rw : forall x, inc x zNum -> forall y, inc y zNum -> 
zLeq x y = exists z, inc z zNum & zLeq z0 z & y = zPlus x z.
Proof.
ir;ap iff_eq;ir.
nin H1.
rwi nLeq_rw H5;nSolveS. nin H5;ee.
exists [J x n0].
ee. ap zNum_inc;nSolveS.
uf z0. rw zLeq_rw;nSolveS.
rw nPlus_0;nSolveS.
rw zPlus_passes;nSolveS.
rw nPlus_0;nSolveS.
ap related_classes_eq;try ap product_pair_inc;nSolveS.
ap zEquiv_equiv.
uhg;clpr. rw H6.
AAC_all.aac_solve_all nPlus_assoc nPlus_comm.

nin H1;ee;subst.
rwi zNum_inc_rw H;nin H;nin H;ee;subst.
rwi zPos_rw H2. nin H2;ee;subst.
rw zPlus_passes;nSolveS. rw zLeq_rw;nSolveS.
rw nPlus_0;nSolveS. rw nLeq_rw;nSolveS.
 exists x;ee. am.
AAC_all.aac_solve_all nPlus_assoc nPlus_comm.
Qed.

Lemma zLeq_trans : transitiveT zLeq zNum.
Proof.
uhg;ir.
rwi zLeq_ex_rw H1;try am. rwi zLeq_ex_rw H3;try am.
rw zLeq_ex_rw;try am.
nin H1;nin H3;ee;subst.
exists (zPlus x0 x1).
ee. ap zPlus_lci;am.

rwi zPos_rw H6. rwi zPos_rw H4. nin H6;nin H4;ee;subst.
rw zPlus_passes;nSolveS. rw nPlus_0;nSolveS.
rw zPos_rw. exists (nPlus x2 x3);ee;nSolveS.
AAC_lci.aac_solve_lci zPlus zPlus_lci zPlus_assoc zPlus_comm;am.
Qed.

Lemma zLeq_order : is_order zLeq zNum.
Proof.
uhg;ee. ap zLeq_refl. ap zLeq_antisym. ap zLeq_trans.
Qed.

Lemma zLeq_etrans : forall x y, zLeq x y -> forall z, zLeq y z -> 
zLeq x z.
Proof.
ir. cp (zLeq_inc H). cp (zLeq_inc H0). ee.
apply zLeq_trans with y;am.
Qed.

Lemma zLeq_total_order : is_total_order zLeq zNum.
Proof.
uhg;ee. ap zLeq_order. ap zLeq_total.
Qed.

Lemma zLeq_zPlus_compat : Ordered_lci.is_compatible zLeq zPlus zNum.
Proof.
ap Ordered_lci.invariant_compat. ap zLeq_order. ap zPlus_lci.
uhg. dj.
uhg;ir.
rwi zLeq_ex_rw H2;try am. nin H2;ee;subst.
rw zLeq_ex_rw;try am;try ap zPlus_lci;try am.
exists x0;ee. am. am.
AAC_lci.aac_solve_lci zPlus zPlus_lci zPlus_assoc zPlus_comm;am.
uhg;ir. rw zPlus_comm;try am. rw (zPlus_comm H0);try am.
ap H;am.
Qed.

Lemma zPlus_ordered : is_ordered_group zLeq zPlus zNum z0.
Proof.
uhg;ee. ap zLeq_order. ap zPlus_group. ap zLeq_zPlus_compat.
Qed.

Lemma zLeq_zPlus_reg : is_order_regular zLeq zPlus zNum.
Proof.
eapply ordered_group_order_regular. ap zPlus_ordered.
Qed.

Definition zLeq_zPlus_reg_l := and_P zLeq_zPlus_reg.
Definition zLeq_zPlus_reg_r := and_Q zLeq_zPlus_reg.

Lemma zOpp_zMult_l : forall a, inc a zNum -> forall b, inc b zNum -> 
zOpp (zMult a b) = zMult (zOpp a) b.
Proof.
ir. uf zOpp.
eapply inverse_ml_insert_left. ap zNum_ring.
am. am.
Qed.

Lemma zOpp_zMult_r : forall a, inc a zNum -> forall b, inc b zNum -> 
zOpp (zMult a b) = zMult a (zOpp b).
Proof.
ir. uf zOpp.
eapply inverse_ml_insert_right. ap zNum_ring.
am. am.
Qed.

Lemma zOpp_zPlus : forall a, inc a zNum -> forall b, inc b zNum -> 
zOpp (zPlus a b) = zPlus (zOpp b) (zOpp a).
Proof.
ir. ap inverse_of_law. ap group_is_monoid;ap zPlus_group.
am. am. ap zPlus_group;am. ap zPlus_group;am.
Qed.

Lemma zOpp_zOpp : forall x, inc x zNum -> zOpp (zOpp x) = x.
Proof.
ir. symmetry. ap inverse_inverse. ap zPlus_group. am.
Qed.

Lemma zOpp_z0 : zOpp z0 = z0.
Proof.
uf z0. ap zOpp_rw;nSolveS.
Qed.

Lemma zMult_integral_neq : forall a, inc a zNum -> z0<>a -> forall b, inc b zNum -> 
z0<>b -> z0<>(zMult a b).
Proof.
uhg;ir. symmetry in H3.
apply zMult_integral in H3;au. nin H3;au.
Qed.

Lemma zLeq_zMult_reg_l : forall a, inc a zNum -> z0<>a -> zLeq z0 a -> 
forall x, inc x zNum -> forall y, inc y zNum -> zLeq (zMult a x) (zMult a y) -> 
zLeq x y.
Proof.
ir.
rwi zNum_inc_rw H2. rwi zNum_inc_rw H3.
nin H2;nin H2;nin H3;nin H3;ee;subst.
rwi zPos_rw H1. nin H1;ee;subst.
rwi zMult_passes H4;nSolveS.
rwi zMult_passes H4;nSolveS.
rwi zLeq_rw H4;nSolveS.
rw zLeq_rw;nSolveS.
rwi nMult_0_l H4. rwi nMult_0_l H4.
rwi nMult_0_l H4. rwi nMult_0_l H4.
rwi nPlus_0_l H4;nSolveS.
rwi nPlus_0_l H4;nSolveS.
rwi nPlus_0 H4;nSolveS.
rwi nPlus_0 H4;nSolveS.
assert (x<>n0).
uhg;ir;subst;ap H0;tv.
wri nMult_distrib_l H4. wri nMult_distrib_l H4.
apply nLeq_nMult_reg_l in H4;nSolveS.
Qed.

Lemma zLeq_zMult_reg_r :  forall a, inc a zNum -> z0<>a -> zLeq z0 a -> 
forall x, inc x zNum -> forall y, inc y zNum -> zLeq (zMult x a) (zMult y a) -> 
zLeq x y.
Proof.
ir.
apply zLeq_zMult_reg_l with a;try am.
rw zMult_comm;try am. rw (zMult_comm H H3). am.
Qed.

Import Ordered_ring.

Lemma zNum_oring : is_ordered_ring zPlus zMult zLeq zNum z0 z1.
Proof.
uhg;ee. ap zNum_ring. ap zLeq_order. ap zLeq_zPlus_compat.
uf z0;uf z1. rw zLeq_rw;nSolveS.
rw nPlus_0;nSolveS.
ap zLeq_zMult_preserves.
Qed.

Lemma zLeq_zMult_l : forall a, inc a zNum -> zLeq z0 a -> forall b, inc b zNum -> forall c, inc c zNum -> 
zLeq b c -> zLeq (zMult a b) (zMult a c).
Proof.
ap (oring_ml_lcompat zNum_oring).
Qed.

Lemma zLeq_zOpp : forall x, inc x zNum -> forall y, inc y zNum -> 
zLeq x y = zLeq (zOpp y) (zOpp x).
Proof.
ir. rwi zNum_inc_rw H;rwi zNum_inc_rw H0.
nin H;nin H;nin H0;nin H0;ee;subst.
rw zLeq_rw;nSolveS.
rw zOpp_rw;try am. rw zOpp_rw;try am.
rw zLeq_rw;try am.
ap uneq2;ap nPlus_comm.
Qed.

Lemma zNum_pos_pow : forall a, inc a nNum -> [J a n0] = pow zPlus z0 z1 a.
Proof.
ap nNum_rect.
rw pow_0. tv.
ir.
rw pow_S. wr H0. uf z1. rw zPlus_passes;nSolveS.
rw nPlus_0_l;nSolveS.
ap uneq. ap uneq2;au.
rw nPlus_comm;nSolveS. uf n1. rw nPlus_S;nSolveS.
rw nPlus_0;nSolveS.
am.
Qed.

Lemma zNum_neg_pow : forall a, inc a nNum -> [J n0 a] = pow zPlus z0 (zOpp z1) a.
Proof.
ir. wr zOpp_rw;nSolveS. rw zNum_pos_pow;nSolveS. 
ap pow_group_inverse. ap zPlus_group. ap z1_inc. am.
Qed.

Lemma zNum_nNum_pr : forall x, inc x zNum -> 
(exists n, inc n nNum & x = pow zPlus z0 z1 n)\/(exists n, inc n nNum & x = pow zPlus z0 (zOpp z1) n).
Proof.
ir.
rwi zNum_pos_neg H.
nin H;nin H;ee;subst.
left. exists x0;ee. am. ap zNum_pos_pow. am.
right. exists x0;ee. am. ap zNum_neg_pow. am.
Qed.

Lemma zNum_pow_pos : forall n, inc n nNum -> zLeq z0 (pow zPlus z0 z1 n).
Proof.
ir. wr zNum_pos_pow. uf z0. constructor;nSolveS.
rw nPlus_0;nSolveS. am.
Qed.

Lemma zNum_pow_neg : forall n, inc n nNum -> zLeq (pow zPlus z0 (zOpp z1) n) z0.
Proof.
ir. wr zNum_neg_pow. uf z0. constructor;nSolveS.
rw nPlus_0;nSolveS. am.
Qed.

Lemma zNum_pow_pos_eq : forall n, inc n nNum -> forall m, inc m nNum -> 
pow zPlus z0 z1 n = pow zPlus z0 z1 m -> n=m.
Proof.
ir. wri zNum_pos_pow H1;au.  wri zNum_pos_pow H1;au.
apply class_of_eq_related in H1. uh H1;clpri H1.
rwi nPlus_0 H1;nSolveS. rwi nPlus_0 H1;nSolveS.
ap zEquiv_equiv.
ap product_pair_inc;nSolveS.
ap product_pair_inc;nSolveS.
Qed.

Lemma zOpp_inj : Transformation.injects zNum zOpp.
Proof.
uhg;ir.
cp (uneq zOpp H1).
rwi zOpp_zOpp H2;au. rwi zOpp_zOpp H2;au.
Qed.

Lemma zNum_pow_neg_eq : forall n, inc n nNum -> forall m, inc m nNum -> 
pow zPlus z0 (zOpp z1) n = pow zPlus z0 (zOpp z1) m -> n=m.
Proof.
ir.
ufi zOpp H1;wri pow_group_inverse H1.
ufi zOpp H1;wri pow_group_inverse H1.
fold zOpp in H1. apply zOpp_inj in H1.
ap zNum_pow_pos_eq. am. am. am.
ap pow_inc. ap zPlus_monoid;am. ap z1_inc. am.
ap pow_inc. ap zPlus_monoid;am. ap z1_inc. am.
ap zPlus_group.
ap z1_inc.
am. ap zPlus_group. ap z1_inc. am.
Qed.

Lemma zNum_pow_neg_pos : forall n, inc n nNum -> forall m, inc m nNum -> 
pow zPlus z0 z1 n = pow zPlus z0 (zOpp z1) m -> (n=n0 & m=n0).
Proof.
ir.
cp (zNum_pow_pos H).
cp (zNum_pow_neg H0).
wri H1 H3.
assert (pow zPlus z0 z1 n = z0).
apply zLeq_antisym. ap pow_inc. ap zPlus_monoid. ap z1_inc. am.
ap z0_inc. am. am.
ee.
ap zNum_pow_pos_eq. am. ap n0_inc.
rw pow_0. am.
ap zNum_pow_neg_eq. am. ap n0_inc.
rw pow_0. wr H1.
 am.
Qed.

Lemma zLeq_z0_z1 : zLeq z0 z1.
Proof.
constructor;nSolveS.
repeat rw nPlus_0;nSolveS.
Qed.

End NotaSec.

Ltac zSolve := match goal with
  | |- inc (nPlus _ _) nNum => ap nPlus_lci;zSolve
  | |- inc (nMult _ _) nNum => ap nMult_lci;zSolve
  | |- inc (oS _) nNum => ap oS_nNum;zSolve
  | |- inc emptyset nNum => ap emptyset_N
  | |- inc n0 nNum => ap n0_inc
  | |- inc _ nNum => nSolveS
  | |- inc (zPlus _ _) zNum => ap zPlus_lci;zSolve
  | |- inc (zMult _ _) zNum => ap zMult_lci;zSolve
  | |- inc (zOpp _) zNum => ap zOpp_inc;zSolve
  | |- inc z0 zNum => ap z0_inc
  | |- inc z1 zNum => ap z1_inc
  | |- z0 <> z1 => ap z0_z1_neq
  | |- z1 <> z0 => uhg;intro zSolveH;ap z0_z1_neq;symmetry;am
  | |- zLeq z0 z1 => ap zLeq_z0_z1
  | |- zLeq ?z ?z => ap zLeq_refl;zSolve
  | |- inc (class_of (product nNum nNum) (zEquiv) (J ?a ?b)) zNum => ap zNum_inc;zSolve
  | |- inc _ zNum => try am
  | _ => tv
  end.

Section NotaSec2.

Notation "[ x ]" := (class_of zEquiv (product nNum nNum) x).

Definition zPos := Z zNum (zLeq z0).

Inductive in_zPos : E -> Prop :=
  | z0_in_zPos : in_zPos z0
  | S_in_zPos : forall z, in_zPos z -> in_zPos (zPlus z z1)
.

Lemma zPos_in_zPos : forall z, inc z zPos -> in_zPos z.
Proof.
assert (forall n, inc n nNum -> in_zPos [J n n0]).
ap nNum_rect.
constructor.
ir. set (z := [J n n0]) in *.
replace [J (oS n) n0] with (zPlus z z1).
constructor. am.
uf z. uf z1. rw zPlus_passes;nSolveS.
rw nPlus_0. uf n1;rw nPlus_S. rw nPlus_0.
tv. am. am. nSolveS. nSolveS.

ir. apply Z_all in H0. ee.
rwi zPos_rw H1. nin H1;ee;subst;au.
Qed.

Lemma in_zPos_zPos : forall z, in_zPos z -> inc z zPos.
Proof.
ir. nin H;ap Z_inc;zSolve.
apply Z_all in IHin_zPos. ee. am.
apply Z_all in IHin_zPos; ee.
apply zLeq_trans with (zPlus z0 z1);zSolve.
rw zPlus_z0_l;zSolve. 
ap zLeq_zPlus_compat;zSolve.
Qed.

Lemma zNum_disj : forall z, inc z zNum -> (inc z zPos \/ inc (zOpp z) zPos).
Proof.
ir. nin (zLeq_total z0_inc H).
left. ap Z_inc;am.
right. ap Z_inc;zSolve.
wr zOpp_z0. wr zLeq_zOpp;zSolve.
Qed.

End NotaSec2.

End ZTemp.

