
Set Implicit Arguments.
Unset Strict Implicit.

Require Import qtemp.
Require Import aac.
Require Export nnum_base.

Module qEmbed.
Import QTemp.
Import Ordered_lci.
Import Pow.
Import nNum_ring.

Definition qNat n := pow qPlus q0 q1 n.

Lemma qNat_inc : forall n, inc n nNum -> inc (qNat n) qNum.
Proof.
ap pow_inc. ap qPlus_monoid. ap q1_inc.
Qed.

Lemma qNat_pos : forall n, inc n nNum -> qLeq q0 (qNat n).
Proof.
ap nNum_rect;uf qNat;ir.
rw pow_0. ap qLeq_refl;qSolve.
rw pow_S;au.
assert (qLeq (qPlus q0 q0) (qPlus q1 (pow qPlus q0 q1 n))).
ap qLeq_qPlus_compat;qSolve.
ap qNat_inc. am.
rwi qPlus_0_l H1;au. ap q0_inc.
Qed.

Lemma qNat_nonzero : forall n, inc n nNum -> n<>n0 -> qNat n <> q0.
Proof.
ir. apply nNum_destruct in H. nin H. subst.
nin H0;tv.
nin H;ee;subst.
uf qNat.
uhg;ir. rwi pow_S H1;qSolve.
ap q0_q1_neq. ap qLeq_antisym;qSolve.
rw qLeq_qOpp;qSolve. rw qOpp_q0.
replace (qOpp q1) with (pow qPlus q0 q1 x).
ap qNat_pos. am.
apply qPlus_reg_l with q1;qSolve.
ap qNat_inc;am.
rw qOpp_r;au. ap q1_inc.
Qed.

Lemma qNat_nPlus : forall n, inc n nNum -> forall m, inc m nNum -> 
qNat (nPlus n m) = qPlus (qNat n) (qNat m).
Proof.
eapply pow_nPlus. ap qPlus_monoid. ap q1_inc.
Qed.

Lemma qNat_unicity : forall n, inc n nNum -> forall m, inc m nNum -> 
qNat n = qNat m -> n=m.
Proof.
pose (p := fun n => forall m : E, (m ∈ ω) -> qNat n = qNat m -> n = m).
assert (forall n, inc n nNum -> p n);try am.
ap nNum_rect;uf p;uf qNat;ir.
rwi pow_0 H0.
apply nNum_destruct in H. nin H;ee;subst. tv.
nin H;ee;subst.
destruct qNat_nonzero with (oS x).
ap oS_nNum;am. uhg;ir.
apply emptyset_empty with x. ufi n0 H1. wr H1. rw oS_inc. au.
au.
apply nNum_destruct in H1. nin H1. subst.
rwi pow_0 H2. apply qNat_nonzero in H2.
elim H2.
ap oS_nNum;am. uhg;ir.
apply emptyset_empty with n. ufi n0 H1. wr H1. rw oS_inc. au.
nin H1;ee;subst. ap uneq.
ap H0. am.
rwi pow_S H2;au. rwi pow_S H2;au.
apply qPlus_reg_l with q1;qSolve;ap qNat_inc;am.
Qed.

Definition qNat_back x := unique_choose (fun n => inc n nNum & x = qNat n).

Lemma qNat_back_pr : forall n, inc n nNum -> (inc (qNat_back (qNat n)) nNum & qNat n = qNat (qNat_back (qNat n))).
Proof.
ir;uf qNat_back. ap unique_choose_pr.
exists n;ee;au.
uhg;ir. ee.
ap qNat_unicity. am. am. transitivity (qNat n);au.
Qed.

Lemma qNat_back_qNat : forall n, inc n nNum -> qNat_back (qNat n) = n.
Proof.
ir.
cp (qNat_back_pr H).
ee.
ap qNat_unicity;au.
Qed.

Lemma qNat_back_Im : forall x, inc x (Im qNat nNum) -> (inc (qNat_back x) nNum &
x = qNat (qNat_back x)).
Proof.
ir. Im_nin H. subst.
ap qNat_back_pr. am.
Qed.

Lemma qNat_back_inc : forall x, inc x (Im qNat nNum) -> inc (qNat_back x) nNum.
Proof.
ir;ap qNat_back_Im;am.
Qed.

Definition qEmbedder0 x := if P_dec (inc x (Im qNat nNum))
then qNat_back x
else x.

Lemma qEmbedder0_injects : Transformation.injects qNum qEmbedder0.
Proof.
uhg;ir.
ufi qEmbedder0 H1.
 destruct (P_dec (inc x (Im qNat nNum))); destruct (P_dec (inc y (Im qNat nNum))).
apply Im_ex in i. apply Im_ex in i0.
nin i;nin i0. ee. subst.
ap uneq.
rwi qNat_back_qNat H1;au. rwi qNat_back_qNat H1;au.
apply Im_ex in i;nin i;ee;subst.
apply qNum_nNum_neq in H0. elim H0.
ap qNat_back_pr. am.
subst. apply qNum_nNum_neq in H.
elim H. ap qNat_back_inc. am.
am.
Qed.

Definition qEmbedder := L qNum qEmbedder0.

Definition qEmbed := Im qEmbedder0 qNum.

Lemma qEmbedder_bij : bijective qNum qEmbed qEmbedder.
Proof.
ap map_of_bijective.
uhg;ee. uhg;ir.
ap Im_inc;am.
ap qEmbedder0_injects.
uhg;ir. Im_nin H.
subst. exists x;ee;au.
Qed.

Definition nEmbedder := inverse (qEmbedder).

Lemma nEmbedder_bij : bijective qEmbed qNum nEmbedder.
Proof.
ap bijective_inverse_bijective. ap qEmbedder_bij.
Qed.

Lemma qEmbedder_inv : are_inverse qNum qEmbed qEmbedder nEmbedder.
Proof.
ap bijective_inverse_of. ap qEmbedder_bij.
Qed.

Lemma nNum_sub_qEmbed : sub nNum qEmbed.
Proof.
uhg;ir.
ap Im_show_inc. exists (qNat a);ee. ap qNat_inc;am.
uf qEmbedder0. rw P_dec_if.
symmetry. ap qNat_back_qNat. am.
ap Im_inc;am.
Qed.

Lemma nEmbedder_nat : forall n, inc n nNum -> ev nEmbedder n = qNat n.
Proof.
ir.
assert (ev qEmbedder (ev nEmbedder n) = n).
ap qEmbedder_inv. ap nNum_sub_qEmbed. am.
ap qEmbedder_bij. eapply trans_of_map. ap nEmbedder_bij.
ap nNum_sub_qEmbed. am.
ap qNat_inc;am.
rw H0.
uf qEmbedder. rw create_ev. uf qEmbedder0.
rw P_dec_if. symmetry. ap qNat_back_qNat. am.
ap Im_inc;am. ap qNat_inc;am.
Qed.

Definition qEPlus x y := ev qEmbedder (qPlus (ev nEmbedder x) (ev nEmbedder y)).
Definition qEMult x y := ev qEmbedder (qMult (ev nEmbedder x) (ev nEmbedder y)).

Lemma qEPlus_lci : is_lci qEPlus qEmbed.
Proof.
uhg;ir.
uf qEPlus. eapply trans_of_map. ap qEmbedder_bij.
ap qPlus_lci. eapply trans_of_map;[ap nEmbedder_bij | am].
eapply trans_of_map;[ap nEmbedder_bij | am].
Qed.

Lemma qEMult_lci : is_lci qEMult qEmbed.
Proof.
uhg;ir.
uf qEMult. eapply trans_of_map. ap qEmbedder_bij.
ap qMult_lci. eapply trans_of_map;[ap nEmbedder_bij | am].
eapply trans_of_map;[ap nEmbedder_bij | am].
Qed.

Lemma qEPlus_comm : commutative qEPlus qEmbed.
Proof.
uhg;ir.
uf qEPlus.
ap uneq. ap qPlus_comm.
eapply trans_of_map;[ap nEmbedder_bij | am].
eapply trans_of_map;[ap nEmbedder_bij | am].
Qed.

Lemma qEMult_comm : commutative qEMult qEmbed.
Proof.
uhg;ir.
uf qEMult.
ap uneq. ap qMult_comm.
eapply trans_of_map;[ap nEmbedder_bij | am].
eapply trans_of_map;[ap nEmbedder_bij | am].
Qed.

Lemma qEmbed_0 : ev qEmbedder q0 = n0.
Proof.
uf qEmbedder. rw create_ev;qSolve.
uf qEmbedder0. rw P_dec_if.
replace q0 with (qNat n0). ap qNat_back_qNat;nSolveS.
uf qNat. ap pow_0.
apply Im_show_inc. exists n0;ee. ap n0_inc.
symmetry. ap pow_0.
Qed.

Lemma nEmbed_0 : ev nEmbedder n0 = q0.
Proof.
wr qEmbed_0. ap qEmbedder_inv. ap q0_inc.
Qed.

Lemma qEmbed_1 : ev qEmbedder q1 = n1.
Proof.
uf qEmbedder;uf qEmbedder0.
rw create_ev;qSolve.
replace q1 with (qNat n1).
rw P_dec_if. ap qNat_back_qNat. ap n1_inc.
ap Im_inc. ap n1_inc. uf qNat;uf n1.
rw pow_S;nSolveS. rw pow_0. ap qPlus_0_r;qSolve.
Qed.

Lemma nEmbed_1 : ev nEmbedder n1 = q1.
Proof.
wr qEmbed_1. ap qEmbedder_inv. ap q1_inc.
Qed.

Lemma qEmbed_plus_morph : forall x, inc x qNum -> forall y, inc y qNum -> 
ev qEmbedder (qPlus x y) = qEPlus (ev qEmbedder x) (ev qEmbedder y).
Proof.
ir.
uf qEPlus. ap uneq2. tv. ap uneq2;symmetry;ap qEmbedder_inv;am.
Qed.

Lemma qEmbed_mult_morph : forall x, inc x qNum -> forall y, inc y qNum -> 
ev qEmbedder (qMult x y) = qEMult (ev qEmbedder x) (ev qEmbedder y).
Proof.
ir.
uf qEMult. ap uneq2. tv. ap uneq2;symmetry;ap qEmbedder_inv;am.
Qed.

Lemma qEmbed_rw : qEmbed = Im (ev qEmbedder) qNum.
Proof.
ap extensionality;uhg;ir;Im_nin H;subst;ap Im_show_inc;exists x;ee;au.
symmetry. ap create_ev;am.
ap create_ev;am.
Qed.

Lemma nEmbed_plus_morph : forall x, inc x qEmbed -> forall y, inc y qEmbed -> 
ev nEmbedder (qEPlus x y) = qPlus (ev nEmbedder x) (ev nEmbedder y).
Proof.
ir. rwi qEmbed_rw H;rwi qEmbed_rw H0.
 Im_nin H. Im_nin H0. subst.
wr qEmbed_plus_morph.
etransitivity. ap qEmbedder_inv. ap qPlus_lci;am.
ap uneq2;symmetry;ap qEmbedder_inv;am. am. am.
Qed.

Lemma nEmbed_mult_morph : forall x, inc x qEmbed -> forall y, inc y qEmbed -> 
ev nEmbedder (qEMult x y) = qMult (ev nEmbedder x) (ev nEmbedder y).
Proof.
ir. rwi qEmbed_rw H;rwi qEmbed_rw H0.
 Im_nin H. Im_nin H0. subst.
wr qEmbed_mult_morph.
etransitivity. ap qEmbedder_inv. ap qMult_lci;am.
ap uneq2;symmetry;ap qEmbedder_inv;am. am. am.
Qed.

Lemma qEPlus_assoc : associative qEPlus qEmbed.
Proof.
uhg;ir.
uf qEPlus.
ap uneq.
cp qEmbedder_inv. uh H2;ee.
uh H4;ee.
rw H4. rw H4.
ap qPlus_assoc;eapply trans_of_map;am.
qSolve;eapply trans_of_map;am.
qSolve;eapply trans_of_map;am.
Qed.

Lemma qEMult_assoc : associative qEMult qEmbed.
Proof.
uhg;ir.
uf qEMult.
ap uneq.
cp qEmbedder_inv. uh H2;ee.
uh H4;ee.
rw H4. rw H4.
ap qMult_assoc;eapply trans_of_map;am.
qSolve;eapply trans_of_map;am.
qSolve;eapply trans_of_map;am.
Qed.

Lemma qEPlus_0_l : forall x, inc x qEmbed -> qEPlus n0 x = x.
Proof.
ir. uf qEPlus.
rw nEmbed_0. rw qPlus_0_l. ap qEmbedder_inv. am.
eapply trans_of_map. ap nEmbedder_bij. am.
Qed.

Lemma qEPlus_0_r : forall x, inc x qEmbed -> qEPlus x n0 = x.
Proof.
ir. etransitivity. ap qEPlus_comm. am. ap nNum_sub_qEmbed. ap n0_inc.
ap qEPlus_0_l;am.
Qed.

Lemma qEPlus_neutre : is_neutre qEPlus qEmbed n0.
Proof.
uhg;ee. ap nNum_sub_qEmbed. ap n0_inc.
ap qEPlus_0_r. ap qEPlus_0_l.
Qed.

Lemma qEMult_1_l : forall x, inc x qEmbed -> qEMult n1 x = x.
Proof.
ir. uf qEMult.
rw nEmbed_1. rw qMult_1_l. ap qEmbedder_inv. am.
eapply trans_of_map. ap nEmbedder_bij. am.
Qed.

Lemma qEMult_1_r : forall x, inc x qEmbed -> qEMult x n1 = x.
Proof.
ir. etransitivity. ap qEMult_comm. am. ap nNum_sub_qEmbed. ap n1_inc.
ap qEMult_1_l;am.
Qed.

Lemma qEMult_neutre : is_neutre qEMult qEmbed n1.
Proof.
uhg;ee. ap nNum_sub_qEmbed. ap n1_inc.
ap qEMult_1_r. ap qEMult_1_l.
Qed.

Lemma qEMult_0_l : forall x, inc x qEmbed -> qEMult n0 x = n0.
Proof.
ir.
uf qEMult. rw nEmbed_0.
rw qMult_0_l. ap qEmbed_0.
eapply trans_of_map. ap nEmbedder_bij.
am.
Qed.

Lemma qEMult_0_r : forall x, inc x qEmbed -> qEMult x n0 = n0.
Proof.
ir.
uf qEMult. rw nEmbed_0.
rw qMult_0_r. ap qEmbed_0.
eapply trans_of_map. ap nEmbedder_bij.
am.
Qed.

Definition qEmbed_nEmbed := and_Q (and_Q (and_Q qEmbedder_inv)).
Definition nEmbed_qEmbed := and_P (and_Q (and_Q qEmbedder_inv)).

Lemma qEPlus_inversible : forall x, inc x qEmbed -> inversible qEPlus qEmbed n0 x.
Proof.
ir.
rwi qEmbed_rw H. Im_nin H;subst.
exists (ev qEmbedder (qOpp x0)).
uhg;dj. eapply trans_of_map. ap qEmbedder_bij. am.
eapply trans_of_map. ap qEmbedder_bij. qSolve.
uf qEPlus. rw nEmbed_qEmbed;qSolve.
rw nEmbed_qEmbed;qSolve. rw qOpp_r;qSolve. ap qEmbed_0.
wr H2. ap qEPlus_comm;au. 
Qed.

Lemma qEPlus_monoid : is_monoid qEPlus qEmbed n0.
Proof.
uhg;ee. ap qEPlus_lci. ap qEPlus_neutre. ap qEPlus_assoc.
Qed.

Lemma qEPlus_group : is_group qEPlus qEmbed n0.
Proof.
uhg;ee;try ap qEPlus_monoid. ap qEPlus_inversible. 
Qed.

Lemma qEMult_monoid : is_monoid qEMult qEmbed n1.
Proof.
uhg;ee. ap qEMult_lci. ap qEMult_neutre. ap qEMult_assoc.
Qed.

Lemma qEMult_distrib_l : distrib_l qEPlus qEMult qEmbed.
Proof.
uhg;ir.
uf qEPlus;uf qEMult.
rw nEmbed_qEmbed;qSolve.
rw nEmbed_qEmbed;qSolve. rw nEmbed_qEmbed;qSolve.
ap uneq. ap qMult_distrib_l.
apply (bijective_of_map nEmbedder_bij); am.
apply (bijective_of_map nEmbedder_bij); am.
apply (bijective_of_map nEmbedder_bij); am.
apply (bijective_of_map nEmbedder_bij); am.
apply (bijective_of_map nEmbedder_bij); am.
apply (bijective_of_map nEmbedder_bij); am.
apply (bijective_of_map nEmbedder_bij); am.
apply (bijective_of_map nEmbedder_bij); am.
apply (bijective_of_map nEmbedder_bij); am.
Qed.


Lemma qEMult_distrib_r : distrib_r qEPlus qEMult qEmbed.
Proof.
uhg;ir.
rw qEMult_comm. rw qEMult_distrib_l.
ap uneq2;ap qEMult_comm;am.
am. am. am. ap qEPlus_lci;am. am.
Qed.

Lemma qEMult_distributes : distributes qEPlus qEMult qEmbed.
Proof.
uhg;ee. ap qEMult_distrib_l. ap qEMult_distrib_r.
Qed.

Lemma qEmbed_ring : is_ring qEPlus qEMult qEmbed n0 n1.
Proof.
uhg;ee. ap qEPlus_group. ap qEPlus_comm. ap qEMult_monoid.
 ap qEMult_distributes.
Qed.

Lemma qEMult_inversible : forall x, inc x qEmbed -> x<>n0 -> 
inversible qEMult qEmbed n1 x.
Proof.
ir.
rwi qEmbed_rw H. Im_nin H.
subst.
assert (x0<>q0).
uhg;ir;subst. ap H0. ap qEmbed_0.
exists (ev qEmbedder (qInv x0)).
uhg;dj.
ap (bijective_of_map qEmbedder_bij).
am.
ap (bijective_of_map qEmbedder_bij).
qSolve.
uf qEMult.
rw nEmbed_qEmbed;qSolve. rw nEmbed_qEmbed;qSolve.
rw qInv_r;qSolve. ap qEmbed_1.
wr H4. ap qEMult_comm;au.
Qed.

Lemma qEmbed_field : is_field qEPlus qEMult qEmbed n0 n1.
Proof.
uhg;ee. ap qEmbed_ring. ap qEMult_inversible.
Qed.

Definition qEmbed_tbij := bijective_of_map qEmbedder_bij.
Definition nEmbed_tbij := bijective_of_map nEmbedder_bij.


Definition qELeq x y := qLeq (ev nEmbedder x) (ev nEmbedder y).

Lemma qELeq_refl : reflexiveT qELeq qEmbed.
Proof.
uhg;ir.
ap qLeq_refl. ap nEmbed_tbij. am.
Qed.

Lemma qELeq_antisym : antisymmetricT qELeq qEmbed.
Proof.
uhg;ir.
uh H1;uh H2.
ap nEmbed_tbij;au.
ap qLeq_antisym;au;ap nEmbed_tbij;am.
Qed.

Lemma qELeq_trans : transitiveT qELeq qEmbed.
Proof.
uhg;ir.
eapply qLeq_trans. Focus 3. am.
ap nEmbed_tbij;am.
ap nEmbed_tbij;am.
ap nEmbed_tbij;am.
am.
Qed.

Lemma qELeq_order : is_order qELeq qEmbed.
Proof.
uhg;ee. ap qELeq_refl. ap qELeq_antisym. ap qELeq_trans.
Qed.

Lemma qELeq_total : is_total qELeq qEmbed.
Proof.
uhg;ir.
ap qLeq_total;ap nEmbed_tbij;am.
Qed.

Lemma qELeq_qEPlus_compat : is_compatible qELeq qEPlus qEmbed.
Proof.
uhg;ir.
uf qEPlus;uf qELeq.
rw nEmbed_qEmbed.
rw nEmbed_qEmbed.
ap qLeq_qPlus_compat;try am.
ap nEmbed_tbij;am.
ap nEmbed_tbij;am.
ap nEmbed_tbij;am.
ap nEmbed_tbij;am.
ap qPlus_lci;ap nEmbed_tbij;am.
ap qPlus_lci;ap nEmbed_tbij;am.
Qed.

Import Ordered_ring.

Lemma qELeq_qEMult_preserves : order_preserves qELeq qEMult qEmbed n0.
Proof.
uhg;ir.
uhg. rw nEmbed_0.
uh H0;uh H2. rwi nEmbed_0 H0. rwi nEmbed_0 H2.
uf qEMult.
rw nEmbed_qEmbed;qSolve.
ap qLeq_qMult_preserves.
ap nEmbed_tbij;am.
am. ap nEmbed_tbij;am. am.
ap nEmbed_tbij;am.
ap nEmbed_tbij;am.
Qed.

Lemma qEPlus_ordered : is_ordered_group qELeq qEPlus qEmbed n0.
Proof.
uhg;ee. ap qELeq_order. ap qEPlus_group.
ap qELeq_qEPlus_compat.
Qed.

Lemma qEmbed_ordered : is_ordered_field qEPlus qEMult qELeq qEmbed n0 n1.
Proof.
uhg;ee. ap qEmbed_field. ap qELeq_order. ap qELeq_qEPlus_compat.
uhg. rw nEmbed_0. rw nEmbed_1.
qSolve.
ap qELeq_qEMult_preserves.
Qed.

Lemma qEPlus_nPlus_eq : forall n, inc n nNum -> forall m, inc m nNum -> 
qEPlus n m = nPlus n m.
Proof.
ir. uf qEPlus.
rw nEmbedder_nat;nSolveS. rw nEmbedder_nat;nSolveS.
wr qNat_nPlus;nSolveS. wr nEmbedder_nat;nSolveS.
ap qEmbed_nEmbed. ap nNum_sub_qEmbed;nSolveS.
Qed.

Lemma qEMult_nMult_eq : forall n, inc n nNum -> forall m, inc m nNum -> 
qEMult n m = nMult n m.
Proof.
intros n Hn. ap nNum_rect.
fold n0. rw nMult_0. ap qEMult_0_r.
ap nNum_sub_qEmbed;am.
ir.
rw nMult_S;nSolveS.
replace (oS n2) with (qEPlus n2 n1).
rw qEMult_distrib_l.
rw H0. rw qEMult_1_r.
ap qEPlus_nPlus_eq;nSolveS.
ap nNum_sub_qEmbed;nSolveS.
ap nNum_sub_qEmbed;nSolveS.
ap nNum_sub_qEmbed;nSolveS.
ap nNum_sub_qEmbed;nSolveS.
rw qEPlus_nPlus_eq. uf n1. rw nPlus_S;nSolveS.
rw nPlus_0;nSolveS. am. nSolveS.
Qed.

Lemma qNat_qLeq : forall n, inc n nNum -> forall m, inc m nNum -> nLeq n m -> 
qLeq (qNat n) (qNat m).
Proof.
ir. rwi nLeq_rw H1;au. nin H1;ee;subst.
apply qLeq_qPlus_reg_l with (qOpp (qNat n));qSolve;try ap qNat_inc;au.
rw qNat_nPlus;au.
cp qNat_inc.
rw qPlus_assoc;qSolve;au.
rw qOpp_l;au. rw qPlus_0_l;au.
ap qNat_pos. am.
Qed.

Lemma qELeq_nLeq_eq : forall n, inc n nNum -> forall m, inc m nNum -> 
qELeq n m = nLeq n m.
Proof.
ir;ap iff_eq;ir.
uh H1.
rwi nEmbedder_nat H1;au. rwi nEmbedder_nat H1;au.
rw (leq_not_lt nLeq_to);au.
uhg;ir. nin H2.
cp H2. apply qNat_qLeq in H4;au.
ap H3. ap qNat_unicity;au.
ap qLeq_antisym;au;ap qNat_inc;am.

uhg.
rw nEmbedder_nat;au. rw nEmbedder_nat;au.
ap qNat_qLeq;am.
Qed.

End qEmbed.

Module QETemp.
Import qEmbed.
Import Ordered_lci.
Import Pow.
Import nNum_ring.

Inductive is_fraction : EP :=
  | nat_fraction : forall n, inc n nNum -> is_fraction n
  | opp_fraction : forall x, is_fraction x -> is_fraction (inverse_of qEPlus qEmbed n0 x)
  | div_fraction : forall x, is_fraction x -> forall y, is_fraction y -> n0<>y -> 
       is_fraction (qEMult x (inverse_of qEMult qEmbed n1 y))
.

Definition qNum := Z qEmbed is_fraction.

Lemma nNum_qNum : sub nNum qNum.
Proof.
uhg;ir. ap Z_inc. ap nNum_sub_qEmbed. am.
constructor. am.
Qed.

Lemma q0_inc : inc n0 qNum.
Proof.
ap nNum_qNum;nSolveS.
Qed.

Lemma q1_inc : inc n1 qNum.
Proof.
ap nNum_qNum;nSolveS.
Qed.

Definition qPlus := qEPlus.

Definition qMult := qEMult.

Definition qLeq := qELeq.
(*???*)
Lemma qPlus_lci : is_lci qPlus qNum.
Proof.
uhg;ir. apply Z_all in H;apply Z_all in H0. ee.
ap Z_inc. ap qEPlus_lci.
am. am.

Qed.




End QETemp.



