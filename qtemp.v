
Set Implicit Arguments.
Unset Strict Implicit.

Require Import ztemp.
Require Import aac.

Import AAC_lci.

Module QTemp.
Import ZTemp.
Export Quotient.
Import Ordered_lci.
Import Finite.

Section NotaSec.

(*a/b = c/d iff ad=bc*)
Definition qEquiv x y := let a := P x in let b := Q x in let c := P y in let d := Q y in
zMult a d = zMult b c.

Definition qNum := quotient qEquiv (product zNum (Z zNum (fun x => z0<>x))).

Definition zStar := Z zNum (fun x => z0<>x).

Notation "[ x ]" := (class_of qEquiv (product zNum zStar) x).

Lemma zStar_inc : forall x, inc x zNum -> z0<>x -> inc x zStar.
Proof.
ap Z_inc.
Qed.

Lemma z1_zStar : inc z1 zStar.
Proof.
ap zStar_inc;zSolve.
Qed.

Lemma qNum_inc : forall a, inc a zNum -> forall b, inc b zNum -> z0<>b -> inc [J a b] qNum.
Proof.
ir.
ap class_of_in_quotient. ap product_pair_inc. am. ap zStar_inc;am.
Qed.

Lemma qNum_inc1 : forall a, inc a zNum -> inc [J a z1] qNum.
Proof.
ir. ap qNum_inc. am. zSolve. ap z0_z1_neq.
Qed.

Definition q0 := [J z0 z1].

Definition q1 := [J z1 z1].

Lemma q0_inc : inc q0 qNum.
Proof.
ap qNum_inc1;zSolve.
Qed.

Lemma q1_inc : inc q1 qNum.
Proof.
ap qNum_inc1;zSolve.
Qed.

Lemma qEquiv_refl : reflexiveT qEquiv (product zNum zStar).
Proof.
uhg. ir. product_nin H.
subst. uhg. clpr. apply Z_sub in H1. ap zMult_comm; am.
Qed.

Lemma qEquiv_sym : symmetricT qEquiv (product zNum zStar).
Proof.
uhg;ir.
product_nin H;product_nin H0. subst.
uh H1;clpri H1. uhg. clpr.
apply Z_sub in H3;apply Z_sub in H5.
rw zMult_comm;au. wr H1. ap zMult_comm;au.
Qed.

Lemma qEquiv_trans : transitiveT qEquiv (product zNum zStar).
Proof.
uhg;ir.
product_nin H;product_nin H0;product_nin H2. subst.
apply Z_all in H5;apply Z_all in H7;apply Z_all in H9.
ee.
uh H3;uh H1;uhg;clpri H1;clpri H3;clpr.
apply zMult_reg_r with x3;zSolve.
au.
transitivity (zMult (zMult x0 x3) x5).
wr zMult_assoc;zSolve.
wr zMult_assoc;zSolve. ap uneq. ap zMult_comm;zSolve.
rw H1. symmetry. wr zMult_assoc;zSolve.
rw (zMult_comm H8);zSolve. wr H3.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
Qed.

Lemma qEquiv_equiv : is_equivalence qEquiv (product zNum zStar).
Proof.
uhg;ee. ap qEquiv_refl. ap qEquiv_sym. ap qEquiv_trans.
Qed.

Lemma qNum_rw : forall x, inc x qNum = (exists a, exists b, inc a zNum & inc b zNum & z0<>b & x=[J a b]).
Proof.
ir;ap iff_eq;ir.
apply Z_pr in H. nin H.
product_nin H. apply Z_all in H1. subst.
ee. exists x0;exists x1;ee;au.
nin H;nin H;ee;subst.
ap qNum_inc;am.
Qed.

Lemma qNum_nNum_neq : forall x, inc x qNum -> inc x nNum -> False.
Proof.
ir.
assert (Finite.is_finite x).
ap nNum_finite.
am.
rwi finite_trans_rw H1.
rwi qNum_rw H. nin H;nin H;ee;subst.
assert (forall n, inc n nNum -> inc (pow zPlus z0 z1 (oS n)) zNum).
ir. ap pow_inc. ap zPlus_monoid. ap z1_inc. ap oS_nNum;am.
assert (forall n, inc n nNum -> z0 <> pow zPlus z0 z1 (oS n)).
ir.
uhg;ir.
assert (n0 <> (oS n)). uhg;ir. 
apply emptyset_empty with n. ufi n0 H7;rw H7. rw oS_inc;au.
ap H7. ap zNum_pow_pos_eq.
ap n0_inc. ap oS_nNum;am. rw pow_0. am.
set (zN := pow zPlus z0 z1) in *.
assert (forall n, inc n nNum -> qEquiv (J x0 x1) (J (zMult (zN (oS n)) x0) (zMult (zN (oS n)) x1))).
ir;uhg;clpr.
AAC_lci.aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;au.
assert (forall n, inc n nNum -> inc (J (zMult (zN (oS n)) x0) (zMult (zN (oS n)) x1)) [J x0 x1]).
ir. ap Z_inc.
ap product_pair_inc. zSolve. au.
ap Z_inc;zSolve;au.
ap zMult_integral_neq;zSolve.
au. au.
au.
assert (forall n, inc n nNum -> forall m, inc m nNum -> 
(J (zMult (zN (oS n)) x0) (zMult (zN (oS n)) x1)) = (J (zMult (zN (oS m)) x0) (zMult (zN (oS m)) x1))
-> n=m).
ir. apply pair_eq in H10;ee.
apply zMult_reg_r in H11;au.
ap oS_N_inj;au.
ap zNum_pow_pos_eq;nSolveS.
clear H6.
pose (kN n := J (zMult (zN (oS n)) x0) (zMult (zN (oS n)) x1)).
pose (cN x := unique_choose (fun n => inc n nNum & x = kN n)).
assert (forall n, inc n nNum -> (inc (cN (kN n)) nNum & kN n = kN (cN (kN n)))).
ir. uf cN. ap unique_choose_pr.
exists n;ee;au.
uhg;ir. ee. rwi H12 H11. au.
pose (f := fun x => if (P_dec (exists n, inc n nNum & x = kN n)) then
kN (oS (cN x))
else x).

assert (Transformation.injective [J x0 x1] [J x0 x1] f).
uhg;ee;uhg;ir.
uf f. destruct (P_dec (exists n : E, n ∈ ω & x = kN n)).
nin e;ee;subst. destruct H6 with x2;au.
ap H7. ap oS_nNum;am.
am.

ufi f H11.
destruct (P_dec (exists n : E, n ∈ ω & x = kN n));
destruct (P_dec (exists n : E, n ∈ ω & y = kN n)).
destruct e;destruct e0;ee;subst.
apply H8 in H11;au.
apply oS_N_inj in H11;au.
cp (uneq kN H11).
destruct H6 with x2;au. destruct H6 with x3;au.
wri H16 H14. wri H18 H14. am.
ap H6. am. ap H6;am.
ap oS_nNum;ap H6;am. ap oS_nNum;ap H6;am.
destruct e. ee. destruct H6 with x2. am.
nin n. exists (oS (cN x)). subst. ee;au.
ap oS_nNum;am.
destruct e;ee;subst.
nin n. econstructor;ee;try reflexivity.
nSolveS. ap H6. am.
am.
apply H1 in H9.
assert (inc (kN n0) [J x0 x1]).
ap H7. ap n0_inc.
apply H9 in H10. nin H10;ee.
ufi f H11.
destruct (P_dec (exists n : E, n ∈ ω & x = kN n)).
nin e;ee;subst.
apply H8 in H11;nSolveS.
apply emptyset_empty with (cN (kN x2)).
ufi n0 H11. wr H11.
rw oS_inc;right;tv.
ap H6. am.
nin n. exists n0;ee. ap n0_inc. am.
Qed.

Definition qMult0 x y := let a := P x in let b := Q x in let c := P y in let d := Q y in
J (zMult a c) (zMult b d).

Lemma qMult0_lci : is_lci qMult0 (product zNum zStar).
Proof.
uhg;ir. product_nin H;product_nin H0.
subst. apply Z_all in H2;apply Z_all in H4;ee.
uf qMult0;clpr.
ap product_pair_inc;zSolve.
ap Z_inc;zSolve. uhg;ir. symmetry in H5.
apply zMult_integral in H5;zSolve. nin H5;subst;au.
Qed.

Lemma qMult0_comm : commutative qMult0 (product zNum zStar).
Proof.
uhg;ir.
product_nin H;product_nin H0;subst;uf qMult0;clpr.
unfold zStar in *;Ztac;Ztac.
ap uneq2;ap zMult_comm;am.
Qed.

Lemma qMult0_compat : is_compatible qEquiv qMult0 (product zNum zStar).
Proof.
ap invariant_transitive_compat.
ap qEquiv_trans.
ap qMult0_lci.
uhg;dj.
uhg;ir.
product_nin H;product_nin H0;product_nin H1. subst.
unfold zStar in *. Ztac. Ztac. Ztac.
uh H2;clpri H2;uhg;uf qMult0;clpr.
transitivity (zMult (zMult x2 x5) (zMult x0 x1)).
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;zSolve.
rw H2.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;zSolve.

uhg;ir. rw qMult0_comm;try am. rw (qMult0_comm H0);try am.
ap H;am.
Qed.

Definition qMult := quotient_op qEquiv (product zNum zStar) 
qEquiv (product zNum zStar) qMult0.

Lemma qMult_passes_p : forall x, inc x (product zNum zStar) -> forall y, inc y (product zNum zStar) -> 
qMult [x] [y] = [qMult0 x y].
Proof.
ap quotient_op_passes;try ap qEquiv_equiv.
ap qMult0_lci.
ap qMult0_compat.
Qed.

Lemma qMult_passes : forall a, inc a zNum -> forall b, inc b zNum -> z0<>b -> 
forall c, inc c zNum -> forall d, inc d zNum -> z0<>d -> 
qMult [J a b] [J c d] = [J (zMult a c) (zMult b d)].
Proof.
ir. rw qMult_passes_p. uf qMult0;clpr.
tv.
ap product_pair_inc. am. ap Z_inc;am.
ap product_pair_inc. am. ap Z_inc;am.
Qed.

Lemma qBase_pr : forall x, inc x (product zNum zStar) -> exists a, exists b, inc a zNum & inc b zNum & 
z0<>b & x=J a b.
Proof.
ir. product_nin H. apply Z_all in H1;ee;subst;exists x0;exists x1;ee;au.
Qed.

Ltac qBase H := apply qBase_pr in H;nin H;nin H;ee.

Lemma qMult_lci : is_lci qMult qNum.
Proof.
uhg;ir.
rwi qNum_rw H;rwi qNum_rw H0.
nin H;nin H;nin H0;nin H0;ee;subst.
rw qMult_passes;try am. ap qNum_inc;zSolve.
ap zMult_integral_neq;zSolve.
Qed.

Lemma qMult_comm : commutative qMult qNum.
Proof.
uhg;ir.
rwi qNum_rw H;rwi qNum_rw H0.
nin H;nin H;nin H0;nin H0;ee;subst.
rw qMult_passes;try am. rw qMult_passes;try am.
rw zMult_comm;try am. rw (zMult_comm H1);try am.
tv.
Qed.

Lemma qMult_assoc : associative qMult qNum.
Proof.
uhg;ir.
rwi qNum_rw H;rwi qNum_rw H0;rwi qNum_rw H1.
nin H;nin H;nin H0;nin H0;nin H1;nin H1;ee;subst.
rw qMult_passes;zSolve.
rw qMult_passes;zSolve.
rw qMult_passes;zSolve.
rw qMult_passes;zSolve.
rw zMult_assoc;try am. rw zMult_assoc;try am. tv.
ap zMult_integral_neq;am. ap zMult_integral_neq;am.
Qed.

Lemma q0_eq : forall a, inc a zNum -> z0<>a -> 
[J z0 a] = q0.
Proof.
ir. ap related_classes_eq. ap qEquiv_equiv.
ap product_pair_inc. ap z0_inc.
ap Z_inc;am.
ap product_pair_inc. ap z0_inc.
ap Z_inc;zSolve.
uhg;clpr.
rw zMult_0_l;zSolve.
rw zMult_0_r;zSolve.
Qed.

Lemma q0_eq_pr : forall a, inc a zNum -> forall b, inc b zNum -> z0<>b -> 
[J a b] = q0 -> a=z0.
Proof.
ir.
apply class_of_eq_related in H2.
uh H2;clpri H2. rwi zMult_1_r H2;try am.
rwi zMult_0_r H2;try am.
ap qEquiv_equiv.
ap product_pair_inc. am. ap Z_inc;am.
ap product_pair_inc;zSolve;ap Z_inc;zSolve.
Qed.

Lemma qMult_0_l : forall x, inc x qNum -> qMult q0 x = q0.
Proof.
ir. rwi qNum_rw H;nin H;nin H;ee;subst.
uf q0. rw qMult_passes;zSolve.
rw zMult_0_l;zSolve. fold q0. ap q0_eq. zSolve. ap zMult_integral_neq;try am.
ap z1_inc. ap z0_z1_neq. 
Qed.

Lemma qMult_0_r : forall x, inc x qNum -> qMult x q0 = q0.
Proof.
ir;rw qMult_comm;try am. ap qMult_0_l;am.
ap q0_inc.
Qed.

Lemma qNum_eq : forall a, inc a zNum -> forall b, inc b zNum -> z0<>b -> 
forall c, inc c zNum -> forall d, inc d zNum -> z0<>d ->
([J a b] = [J c d]) = (qEquiv (J a b) (J c d)).
Proof.
ir. ap iff_eq. ap class_of_eq_related. ap qEquiv_equiv.
ap product_pair_inc. am. ap Z_inc;am.
ap product_pair_inc. am. ap Z_inc;am.
ap related_classes_eq.
ap qEquiv_equiv.
ap product_pair_inc. am. ap Z_inc;am.
ap product_pair_inc. am. ap Z_inc;am.
Qed.

Lemma qNum_eq1 : forall a, inc a zNum -> z0<>a -> [J a a] = q1.
Proof.
ir. uf q1;rw qNum_eq;try am;zSolve.
uhg;clpr. tv. 
Qed.

Lemma qMult_1_l : forall x, inc x qNum -> qMult q1 x = x.
Proof.
ir. rwi qNum_rw H;nin H;nin H;ee;subst.
uf q1. rw qMult_passes;zSolve.
rw zMult_1_l;zSolve. rw zMult_1_l;zSolve. 
Qed.

Lemma qMult_1_r : forall x, inc x qNum -> qMult x q1 = x.
Proof.
ir;rw qMult_comm;try am. ap qMult_1_l;am.
ap q1_inc.
Qed.

Lemma qMult_neutre : is_neutre qMult qNum q1.
Proof.
uhg;ee. ap q1_inc. ap qMult_1_r. ap qMult_1_l.
Qed.

Lemma qMult_monoid : is_monoid qMult qNum q1.
Proof.
uhg;ee. ap qMult_lci. ap qMult_neutre. ap qMult_assoc.
Qed.

Lemma qMult_inversible : forall x, inc x qNum -> x<>q0 -> inversible qMult qNum q1 x.
Proof.
ir. rwi qNum_rw H;nin H;nin H;ee;subst.
assert (z0<>x0). uhg;ir;subst. ap H0.
ap q0_eq. am. am.
exists [J x1 x0]. uhg;ee.
ap qNum_inc;am. ap qNum_inc;am.
rw qMult_passes;zSolve. rw zMult_comm;zSolve.
ap qNum_eq1. zSolve. ap zMult_integral_neq;try am.
rw qMult_passes;zSolve. rw zMult_comm;zSolve.
ap qNum_eq1. zSolve. ap zMult_integral_neq;try am.
Qed.

Definition qInv := inverse_of qMult qNum q1.

Lemma qInv_pr : forall x, inc x qNum -> x<>q0 -> Lci.are_inverse qMult qNum q1 x (qInv x).
Proof.
ir. ap inversible_inverse_of. ap qMult_monoid.
ap qMult_inversible. am. am.
Qed.

Lemma qInv_inc : forall x, inc x qNum -> x<>q0 -> inc (qInv x) qNum.
Proof.
ir. ap qInv_pr. am. am.
Qed.

Lemma q0_q1_neq : q0<>q1.
Proof.
uhg;ir. ufi q1 H. symmetry in H. apply q0_eq_pr in H;zSolve.
ap z0_z1_neq;au.
Qed.

Lemma qInv_neq : forall x, inc x qNum -> x<>q0 -> qInv x <> q0.
Proof.
uhg;ir.
cp (qInv_pr H H0).
uh H2;ee.
rwi H1 H4. rwi qMult_0_r H4;au.
ap q0_q1_neq;am.
Qed.

Lemma qInv_qInv : forall x, inc x qNum -> x<>q0 -> qInv (qInv x) = x.
Proof.
ir. symmetry.
eapply Lci.inverse_unicity.
ap qMult_monoid.
Focus 2. ap qInv_pr. ap qInv_inc;am.
ap qInv_neq;am.
cp (qInv_pr H H0).
uhg;ee;am.
Qed.

Lemma qInv_l : forall x, inc x qNum -> x<>q0 -> qMult (qInv x) x = q1.
Proof.
ir;ap qInv_pr;am.
Qed.

Lemma qInv_r : forall x, inc x qNum -> x<>q0 -> qMult x (qInv x) = q1.
Proof.
ir;ap qInv_pr;am.
Qed.

Lemma qInv_rw : forall a, inc a zNum -> z0<>a -> forall b, inc b zNum -> z0<>b -> 
qInv [J a b] = [J b a].
Proof.
ir.
eapply Lci.inverse_unicity.
ap qMult_monoid. ap qInv_pr.
ap qNum_inc;am. uhg;ir.
apply q0_eq_pr in H3;try am.
subst;au. uhg;ee.
ap qNum_inc;am. ap qNum_inc;am.
rw qMult_passes;try am. rw zMult_comm;try am.
ap qNum_eq1;zSolve.
ap zMult_integral_neq;zSolve.
rw qMult_passes;try am. rw zMult_comm;try am.
ap qNum_eq1;zSolve.
ap zMult_integral_neq;zSolve.
Qed.

(*a/b + c/d = (ad + bc)/(bd)*)
Definition qPlus0 x y := let a := P x in let b := Q x in let c := P y in let d := Q y in
J (zPlus (zMult a d) (zMult b c)) (zMult b d).

Lemma qPlus0_lci : is_lci qPlus0 (product zNum zStar).
Proof.
uhg;ir.
qBase H. qBase H0. subst.
uf qPlus0;clpr. ap product_pair_inc;zSolve.
ap Z_inc. zSolve. ap zMult_integral_neq;am.
Qed.

Lemma qPlus0_comm : commutative qPlus0 (product zNum zStar).
Proof.
uhg;ir. qBase H;qBase H0;subst.
uf qPlus0;clpr.
ap uneq2. rw zPlus_comm;zSolve.
ap uneq2;ap zMult_comm;am.
ap zMult_comm;am.
Qed.

Lemma qPlus0_compat : is_compatible qEquiv qPlus0 (product zNum zStar).
Proof.
ap invariant_transitive_compat.
ap qEquiv_trans.
ap qPlus0_lci.
uhg;dj.
uhg;ir.
qBase H;qBase H0;qBase H1. subst.
uh H2;clpri H2;uhg;uf qPlus0;clpr.
rw zMult_distrib_l;zSolve. rw zMult_distrib_r;zSolve.
replace (zMult (zMult x2 x1) (zMult x5 x1)) with (zMult (zMult x2 x5) (zMult x1 x1)).
rw H2. ap uneq2.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
uhg;ir. rw qPlus0_comm;try am. rw (qPlus0_comm H0 H2).
ap H;am.
Qed.

Definition qPlus := quotient_op qEquiv (product zNum zStar) 
qEquiv (product zNum zStar) qPlus0.

Lemma qPlus_passes_p : forall x, inc x (product zNum zStar) -> forall y, inc y (product zNum zStar) -> 
qPlus [x] [y] = [qPlus0 x y].
Proof.
ap quotient_op_passes. ap qEquiv_equiv.
ap qEquiv_equiv.
ap qPlus0_lci. ap qPlus0_compat.
Qed.

Lemma qPlus_passes : forall a, inc a zNum -> forall b, inc b zNum -> z0<>b -> 
forall c, inc c zNum -> forall d, inc d zNum -> z0<>d -> 
qPlus [J a b] [J c d] = [J (zPlus (zMult a d) (zMult b c)) (zMult b d)].
Proof.
ir.
rw qPlus_passes_p.
uf qPlus0;clpr. tv.
ap product_pair_inc. am. ap Z_inc;am.
ap product_pair_inc. am. ap Z_inc;am.
Qed.

Lemma qPlus_lci : is_lci qPlus qNum.
Proof.
uhg;ir.
rwi qNum_rw H;rwi qNum_rw H0.
nin H;nin H;nin H0;nin H0;ee;subst.
rw qPlus_passes;try am. ap qNum_inc;zSolve.
ap zMult_integral_neq;am.
Qed.

Lemma qPlus_comm : commutative qPlus qNum.
Proof.
uhg;ir.
rwi qNum_rw H;rwi qNum_rw H0.
nin H;nin H;nin H0;nin H0;ee;subst.
rw qPlus_passes;try am.
rw qPlus_passes;try am.
ap uneq. ap uneq2.
rw zPlus_comm;zSolve.
ap uneq2;ap zMult_comm;am.
ap zMult_comm;am.
Qed.

Lemma qPlus_assoc : associative qPlus qNum.
Proof.
uhg;ir.
rwi qNum_rw H;rwi qNum_rw H0;rwi qNum_rw H1.
nin H;nin H;nin H0;nin H0;nin H1;nin H1;ee;subst.
rw qPlus_passes;zSolve. rw qPlus_passes;zSolve.
rw qPlus_passes;zSolve. rw qPlus_passes;zSolve.
ap uneq. ap uneq2.
rw zMult_distrib_l;zSolve.
rw zMult_distrib_r;zSolve.
rw zMult_assoc;zSolve.  rw zMult_assoc;zSolve.
rw zMult_assoc;zSolve. 
ap zPlus_assoc;zSolve.
ap zMult_assoc;am.
ap zMult_integral_neq;am.
ap zMult_integral_neq;am.
Qed.

Lemma qPlus_same_denom : forall a, inc a zNum -> forall b, inc b zNum -> 
forall c, inc c zNum -> z0<>c -> qPlus [J a c] [J b c] = [J (zPlus a b) c].
Proof.
ir. rw qPlus_passes;zSolve.
rw qNum_eq;zSolve.
uhg;clpr.
rw (zMult_comm H1);try am.
wr zMult_distrib_r;zSolve. wr zMult_assoc;zSolve.
ap zMult_comm;zSolve.
ap zMult_integral_neq;zSolve.
Qed.

Lemma qPlus_0_l : forall x, inc x qNum -> qPlus q0 x = x.
Proof.
ir. rwi qNum_rw H;nin H;nin H;ee;subst.
uf q0. rw qPlus_passes;zSolve.
rw zMult_1_l;zSolve. rw zMult_1_l;zSolve.
rw zMult_0_l;zSolve. rw zPlus_z0_l;zSolve.
Qed.

Lemma qPlus_0_r : forall x, inc x qNum -> qPlus x q0 = x.
Proof.
ir;rw qPlus_comm;try am. ap qPlus_0_l;am.
ap q0_inc.
Qed.

Lemma qPlus_neutre : is_neutre qPlus qNum q0.
Proof.
uhg;ee. ap q0_inc. ap qPlus_0_r. ap qPlus_0_l.
Qed.

Lemma qPlus_monoid : is_monoid qPlus qNum q0.
Proof.
uhg;ee. ap qPlus_lci. ap qPlus_neutre. ap qPlus_assoc.
Qed.

Lemma qPlus_inversible : forall x, inc x qNum -> inversible qPlus qNum q0 x.
Proof.
ir. rwi qNum_rw H. nin H;nin H;ee;subst.
exists [J (zOpp x0) x1]. uhg;ee.
ap qNum_inc;am. ap qNum_inc;zSolve.
rw qPlus_same_denom;zSolve. rw zOpp_r;zSolve.
ap q0_eq. am. am.
rw qPlus_same_denom;zSolve. rw zOpp_l;zSolve.
ap q0_eq. am. am.
Qed.

Lemma qPlus_group : is_group qPlus qNum q0.
Proof.
uhg;ee;try ap qPlus_monoid.
ap qPlus_inversible.
Qed.

Definition qOpp := inverse_of qPlus qNum q0.

Lemma qOpp_pr : forall x, inc x qNum -> Lci.are_inverse qPlus qNum q0 x (qOpp x).
Proof.
ap group_inverse_of. ap qPlus_group.
Qed.

Lemma qOpp_rw : forall a, inc a zNum -> forall b, inc b zNum -> z0<>b -> 
qOpp [J a b] = [J (zOpp a) b].
Proof.
ir.
eapply Lci.inverse_unicity.
ap qPlus_monoid.
ap qOpp_pr.
ap qNum_inc;am.
uhg;ee;try ap qNum_inc;try am.
zSolve.
rw qPlus_same_denom;zSolve.
rw zOpp_r;zSolve. ap q0_eq.
am. am.
rw qPlus_same_denom;zSolve.
rw zOpp_l;zSolve. ap q0_eq.
am. am.
Qed.

Lemma qOpp_inc : forall x, inc x qNum -> inc (qOpp x) qNum.
Proof.
ir;ap qOpp_pr;am.
Qed.

Lemma qOpp_l : forall x, inc x qNum -> qPlus (qOpp x) x = q0.
Proof.
ir;ap qOpp_pr;am.
Qed.

Lemma qOpp_r : forall x, inc x qNum -> qPlus x (qOpp x) = q0.
Proof.
ir;ap qOpp_pr;am.
Qed.

Lemma qMult_distrib_l : distrib_l qPlus qMult qNum.
Proof.
uhg;ir.
rwi qNum_rw H;rwi qNum_rw H0;rwi qNum_rw H1.
nin H;nin H;nin H0;nin H0;nin H1;nin H1;ee;subst.
rw qPlus_passes;zSolve.
rw qMult_passes;zSolve.
rw qMult_passes;zSolve. rw qMult_passes;zSolve.
rw qPlus_passes;zSolve.
rw zMult_distrib_l;zSolve.

transitivity (qMult [J x4 x4] [J (zPlus (zMult x3 (zMult x x2)) (zMult x3 (zMult x0 x1)))
   (zMult x4 (zMult x0 x2))] ).
rw qNum_eq1;try am.
symmetry;ap qMult_1_l.
ap qNum_inc. zSolve. zSolve. ap zMult_integral_neq;zSolve.
ap zMult_integral_neq;zSolve.
rw qMult_passes.
ap uneq;ap uneq2.
rw zMult_distrib_l;zSolve.
ap uneq2.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
am. am. am.
zSolve. zSolve.
ap zMult_integral_neq;zSolve.
ap zMult_integral_neq;zSolve.
ap zMult_integral_neq;zSolve.
ap zMult_integral_neq;zSolve.
ap zMult_integral_neq;zSolve.
Qed.

Lemma qMult_distrib_r : distrib_r qPlus qMult qNum.
Proof.
uhg;ir. rw qMult_comm;try am.
rw qMult_distrib_l;try am.
ap uneq2;ap qMult_comm;am.
ap qPlus_lci;am.
Qed.

Lemma qMult_distributes : distributes qPlus qMult qNum.
Proof.
uhg;ee. ap qMult_distrib_l. ap qMult_distrib_r.
Qed.

Lemma qNum_ring : is_ring qPlus qMult qNum q0 q1.
Proof.
uhg;ee. ap qPlus_group. ap qPlus_comm. ap qMult_monoid.
ap qMult_distributes.
Qed.

Lemma qNum_field : is_field qPlus qMult qNum q0 q1.
Proof.
uhg;ee. ap qNum_ring. ap qMult_inversible.
Qed.

Lemma qMult_integral : is_integral qMult qNum q0.
Proof.
ap (field_integral qNum_field).
Qed.

(*a/b <= c/d iff ad <= bc for b, d>=0*)
Inductive qLeq : E2P :=
  | qLeq_in : forall a, inc a zNum -> forall b, inc b zNum -> lt_of zLeq z0 b -> 
forall c, inc c zNum -> forall d, inc d zNum -> lt_of zLeq z0 d -> zLeq (zMult a d) (zMult b c) -> qLeq [J a b] [J c d].

Lemma qLeq_rw : forall a, inc a zNum -> forall b, inc b zNum -> z0<>b -> zLeq z0 b -> 
forall c, inc c zNum -> forall d, inc d zNum -> z0<>d -> zLeq z0 d -> 
qLeq [J a b] [J c d] = zLeq (zMult a d) (zMult b c).
Proof.
ir;ap iff_eq;ir.
inversion H7.
nin H12;nin H15.
rwi qNum_eq H8;zSolve.
rwi qNum_eq H9;zSolve. uh H8;uh H9;clpri H8;clpri H9.
apply zLeq_zMult_reg_l with (zMult b0 d0);zSolve.
ap zMult_integral_neq;am.
ap zLeq_zMult_preserves;zSolve.
replace (zMult (zMult b0 d0) (zMult a d)) with (zMult (zMult b0 a) (zMult d d0)).
wr H8. replace (zMult (zMult b0 d0) (zMult b c)) with 
(zMult (zMult d0 c) (zMult b0 b)).
wr H9.
replace (zMult (zMult a0 b) (zMult d d0)) with (zMult d (zMult b (zMult a0 d0))).
replace  (zMult (zMult c0 d) (zMult b0 b)) with (zMult d (zMult b (zMult b0 c0))).
ap zLeq_zMult_l. am. am. zSolve. zSolve.
ap zLeq_zMult_l;zSolve.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
constructor;try am.
uhg;ee;am. uhg;ee;am.
Qed.

Lemma q0_q1_leq : qLeq q0 q1.
Proof.
constructor;zSolve.
uhg;ee. ap zNum_oring. ap z0_z1_neq.
uhg;ee. ap zNum_oring. ap z0_z1_neq.
rw zMult_0_l;zSolve. rw zMult_1_l;zSolve.
Qed.

Lemma qNum_rw_pos : forall x, inc x qNum = exists a, exists b, inc a zNum & inc b zNum
 & z0<>b & zLeq z0 b & x = [J a b].
Proof.
ir;ap iff_eq;ir.
rwi qNum_rw H. nin H;nin H;ee;subst.
destruct (zLeq_total z0_inc H0).
exists x0;exists x1;ee;au.
rwi zLeq_zOpp H2;zSolve.
rwi zOpp_z0 H2.
exists (zOpp x0);exists (zOpp x1);ee;zSolve.
uhg;ir.
ap H1. wr (zOpp_zOpp H0). wr H3.
symmetry. ap zOpp_z0.
rw qNum_eq;zSolve.
uhg;clpr. wr zOpp_zMult_r;zSolve.
rw zOpp_zMult_l;zSolve. ap zMult_comm;zSolve.
uhg;ir;ap H1. wr (zOpp_zOpp H0). wr H3.
symmetry. ap zOpp_z0.
nin H;nin H;ee;subst;ap qNum_inc;am.
Qed.

Lemma qLeq_refl : reflexiveT qLeq qNum.
Proof.
uhg;ir. rwi qNum_rw_pos H. nin H;nin H;ee;subst.
constructor;tv.
uhg;ee;am. uhg;ee;am.
rw zMult_comm;zSolve.
Qed.

Lemma qLeq_antisym : antisymmetricT qLeq qNum.
Proof.
uhg;ir.
nin H1. nin H4;nin H7.
rwi qLeq_rw H2;tv.
rw qNum_eq;tv.
uhg;clpr.
ap zLeq_antisym;zSolve.
rw zMult_comm;zSolve. rw (zMult_comm H1 H6). am.
Qed.

Lemma qLeq_trans : transitiveT qLeq qNum.
Proof.
uhg;ir.
nin H1. nin H5;nin H8.
rwi qNum_rw_pos H2. nin H2;nin H2;ee;subst.
rwi qLeq_rw H3;tv.
rw qLeq_rw;tv.
apply zLeq_zMult_reg_l with (d);zSolve.
apply zLeq_trans with (zMult x0 (zMult b c));zSolve.
replace (zMult d (zMult a x0)) with (zMult x0 (zMult a d)).
ap zLeq_zMult_l;zSolve.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
replace (zMult x0 (zMult b c)) with (zMult b (zMult c x0)).
replace (zMult d (zMult b x)) with (zMult b (zMult d x)).
ap zLeq_zMult_l;zSolve.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
Qed.

Lemma qLeq_order : is_order qLeq qNum.
Proof.
uhg;ee. ap qLeq_refl. ap qLeq_antisym. ap qLeq_trans.
Qed.

Lemma qLeq_total : is_total qLeq qNum.
Proof.
uhg;ir.
rwi qNum_rw_pos H;rwi qNum_rw_pos H0.
nin H;nin H;nin H0;nin H0. ee;subst.
rw qLeq_rw;zSolve. rw qLeq_rw;zSolve.
rw zMult_comm;zSolve. rw (zMult_comm H5);zSolve.
ap zLeq_total;zSolve.
Qed.

Lemma qLeq_to : is_total_order qLeq qNum.
Proof.
uhg;ee. ap qLeq_order. ap qLeq_total.
Qed.

Lemma qLeq_qPlus_compat : is_compatible qLeq qPlus qNum.
Proof.
ap invariant_compat. ap qLeq_order. ap qPlus_lci.
uhg;dj.
uhg;ir. nin H2. nin H4;nin H7.
rwi qNum_rw_pos H;nin H;nin H;ee;subst.
rw qPlus_passes;zSolve. rw qPlus_passes;zSolve.
rw qLeq_rw;zSolve.
rw zMult_distrib_l;zSolve. rw zMult_distrib_r;zSolve.
rw zPlus_comm;zSolve.
rw (zPlus_comm (x:=(zMult (zMult b x1) (zMult c x1)) ));zSolve.
replace (zMult (zMult b x0) (zMult d x1)) with (zMult (zMult b x1) (zMult d x0)).
ap zLeq_zPlus_compat;zSolve.
replace (zMult (zMult a x1) (zMult d x1))  with (zMult (zMult x1 x1) (zMult a d)).
replace (zMult (zMult b x1) (zMult c x1)) with (zMult (zMult x1 x1) (zMult b c)).
ap zLeq_zMult_l;zSolve.
ap zLeq_zMult_preserves;zSolve.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
aac_solve_lci zMult zMult_lci zMult_assoc zMult_comm;am.
ap zMult_integral_neq;zSolve.
ap zLeq_zMult_preserves;zSolve.
ap zMult_integral_neq;zSolve.
ap zLeq_zMult_preserves;zSolve.

uhg;ir. rw qPlus_comm;try am. rw (qPlus_comm H0 H2).
ap H;am.
Qed.

Lemma qPlus_ogroup : is_ordered_group qLeq qPlus qNum q0.
Proof.
uhg;ee. ap qLeq_order. ap qPlus_group. ap qLeq_qPlus_compat.
Qed.

Lemma qLeq_qPlus_reg : is_order_regular qLeq qPlus qNum.
Proof.
eapply ordered_group_order_regular.
ap qPlus_ogroup.
Qed.

Definition qLeq_qPlus_reg_l := and_P qLeq_qPlus_reg.
Definition qLeq_qPlus_reg_r := and_Q qLeq_qPlus_reg.

Import Ordered_ring.

Lemma qLeq_qMult_preserves : order_preserves qLeq qMult qNum q0.
Proof.
uhg;ir.
rwi qNum_rw_pos H. nin H;nin H;ee;subst.
ufi q0 H0. rwi qLeq_rw H0;zSolve.
rwi zMult_0_l H0;zSolve.
rwi zMult_1_l H0;zSolve.
rwi qNum_rw_pos H1;nin H1;nin H1;ee;subst.
ufi q0 H2;rwi qLeq_rw H2;zSolve.
rwi zMult_0_l H2;zSolve.
rwi zMult_1_l H2;zSolve.
rw qMult_passes;zSolve.
uf q0. rw qLeq_rw;zSolve.
rw zMult_0_l;zSolve. rw zMult_1_l;zSolve.
ap zLeq_zMult_preserves;zSolve.
ap zMult_integral_neq;zSolve.
ap zLeq_zMult_preserves;zSolve.
Qed.

Definition qPlus_reg := group_is_regular qPlus_group.
Definition qPlus_reg_l := and_P qPlus_reg.
Definition qPlus_reg_r := and_Q qPlus_reg.

Definition qMult_reg_l := integral_quasiregular_left qNum_ring qMult_integral.
Definition qMult_reg_r := integral_quasiregular_right qNum_ring qMult_integral.

Lemma qOpp_qOpp : forall x, inc x qNum -> qOpp (qOpp x) = x.
Proof.
symmetry. ap inverse_inverse. ap qPlus_group. am.
Qed.

Lemma qLeq_qOpp : forall x, inc x qNum -> forall y, inc y qNum -> 
qLeq x y = qLeq (qOpp y) (qOpp x).
Proof.
assert (forall x, inc x qNum -> forall y, inc y qNum -> 
qLeq x y -> qLeq (qOpp y) (qOpp x)).
ir. rwi qNum_rw_pos H;rwi qNum_rw_pos H0;nin H;nin H;nin H0;nin H0;ee;subst.
rwi qLeq_rw H1;try am.
rw qOpp_rw;try am. rw qOpp_rw;try am.
rw qLeq_rw; zSolve.
wr zOpp_zMult_l;zSolve. wr zOpp_zMult_r;zSolve.
wr zLeq_zOpp;zSolve.
rw zMult_comm;zSolve. rw (zMult_comm H0);zSolve.
ir;ap iff_eq;ir.
ap H;am.
apply H in H2.
rwi qOpp_qOpp H2. rwi qOpp_qOpp H2.
am. am. am. ap qOpp_inc;am. ap qOpp_inc;am.
Qed.

Lemma qOpp_qMult_l : forall x, inc x qNum -> forall y, inc y qNum -> 
qOpp (qMult x y) = qMult (qOpp x) y.
Proof.
ir. eapply inverse_ml_insert_left. ap qNum_ring.
am. am.
Qed.

Lemma qOpp_qMult_r : forall x, inc x qNum -> forall y, inc y qNum -> 
qOpp (qMult x y) = qMult x (qOpp y).
Proof.
ir. eapply inverse_ml_insert_right. ap qNum_ring.
am. am.
Qed. 

Lemma qLeq_qMult_l : forall a, inc a qNum -> qLeq q0 a -> 
forall b, inc b qNum -> forall c, inc c qNum -> 
qLeq b c -> qLeq (qMult a b) (qMult a c).
Proof.
ir.
assert (qLeq q0 (qPlus c (qOpp b))).
cp (qOpp_r H1). wr H4.
ap qLeq_qPlus_compat.
am. am. am. ap qOpp_inc;am. ap qOpp_inc;am.
ap qLeq_refl;ap qOpp_inc. am.
cp (qLeq_qMult_preserves H H0 (qPlus_lci H2 (qOpp_inc H1)) H4). 
rwi qMult_distrib_l H5.
wri qOpp_qMult_r H5.
apply qLeq_qPlus_reg_r with (qOpp (qMult a b)).
ap qOpp_inc;ap qMult_lci;am.
ap qMult_lci;am.
ap qMult_lci;am.
rw qOpp_r. am.
ap qMult_lci;am. am. am. am. ap qOpp_inc;am. am.
Qed.

Lemma qLeq_qMult_r : forall a, inc a qNum -> qLeq q0 a -> 
forall b, inc b qNum -> forall c, inc c qNum -> 
qLeq b c -> qLeq (qMult b a) (qMult c a).
Proof.
ir. rw qMult_comm;try am.
rw (qMult_comm H2);try am. ap qLeq_qMult_l;am.
Qed.

Lemma qLeq_qMult_reg_l : forall a, inc a qNum -> a<>q0 -> qLeq q0 a -> 
forall x, inc x qNum -> forall y, inc y qNum -> qLeq (qMult a x) (qMult a y) -> 
qLeq x y.
Proof.
ir.
destruct qLeq_total with x y;try am.
cp (qLeq_qMult_l H H1 H3 H2 H5).
assert (qMult a x = qMult a y).
ap qLeq_antisym;try am. ap qMult_lci;am.
ap qMult_lci;am.
apply qMult_reg_l in H7;try am.
subst. ap qLeq_refl;am.
Qed.

Lemma qNum_ofield : is_ordered_field qPlus qMult qLeq qNum q0 q1.
Proof.
uhg;ee. ap qNum_field. ap qLeq_order.
ap qLeq_qPlus_compat. ap q0_q1_leq.
ap qLeq_qMult_preserves.
Qed.

Lemma qMult_integral_neq : forall x, inc x qNum -> q0<>x -> 
forall y, inc y qNum -> q0<>y -> 
q0<>(qMult x y).
Proof.
uhg;ir. symmetry in H3.
apply qMult_integral in H3;au.
nin H3;au.
Qed.

Lemma qOpp_q0 : qOpp q0 = q0.
Proof.
uf q0. rw qOpp_rw;zSolve. rw zOpp_z0. tv.
Qed.

End NotaSec.

Ltac qSolve := match goal with
  | |- q0<>q1 => ap q0_q1_neq
  | |- q1<>q0 => uhg;intro qSolveH;ap q0_q1_neq;symmetry;ap qSolveH
  | |- qLeq q0 q1 => ap q0_q1_leq
  | |- qLeq ?q ?q => ap qLeq_refl;qSolve
  | |- lt_of qLeq q0 q1 => ap conj;qSolve
  | |- q1<>q0 => uhg;ir;ap q0_q1_neq;symmetry;am
  | |- inc q0 qNum => ap q0_inc
  | |- inc q1 qNum => ap q1_inc
  | |- inc (qPlus _ _) qNum => ap qPlus_lci;qSolve
  | |- inc (qMult _ _) qNum => ap qMult_lci;qSolve
  | |- q0<>(qMult _ _) => ap qMult_integral_neq;qSolve
  | |- inc (qOpp _) qNum => ap qOpp_inc;qSolve
  | |- inc (qInv _) qNum => ap qInv_inc;qSolve
  | |- inc _ zNum => zSolve
  | |- inc _ nNum => nNum_ring.nSolveS
  | |- _ => tv
  end.

End QTemp.




