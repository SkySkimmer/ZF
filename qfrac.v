
Set Implicit Arguments.
Unset Strict Implicit.

(*
Here, prove that elements of qNum from qtemp.v are fractions
of 'natural numbers'
Also additional results for qtemp so we don't have to recompile qtemp.v
*)

Require Import ztemp.
Require Import qtemp.
Require Import aac.

Import AAC_lci.

Module QFrac.
Import ZTemp.
Export QTemp.
Export Quotient.
Import Ordered_lci.
Import Finite.

Section NotaSec.

Notation "[ x ]" := (class_of qEquiv (product zNum zStar) x).

Inductive in_qNat : E -> Prop :=
  | q0_in_qNat : in_qNat q0
  | S_in_qNat : forall q, in_qNat q -> in_qNat (qPlus q q1)
.

Definition qNat := Z qNum in_qNat.

Lemma in_qNat_qNat : forall q, in_qNat q -> inc q qNat.
Proof.
ir. nin H;ap Z_inc;qSolve.
constructor.
apply Z_all in IHin_qNat;ee.
am.
constructor;am.
Qed.

Definition qRel := union2 qNat (Im qOpp qNat).

Lemma qNat_qRel : forall q, inc q qNat -> inc q qRel.
Proof.
ir. ap union2_l. am.
Qed.

Lemma qNat_qOpp_qRel : forall q, inc q qNat -> inc (qOpp q) qRel.
Proof.
ir;ap union2_r;ap Im_inc;am.
Qed.

Lemma qRel_qNum : sub qRel qNum.
Proof.
uhg;ir. apply union2_or in H. nin H.
eapply Z_sub;am. Im_nin H. subst.
qSolve. eapply Z_sub;am.
Qed.

Lemma qNat_qNum : sub qNat qNum.
Proof.
ap Z_sub.
Qed.

Lemma in_qNat_qNum : forall q, in_qNat q -> inc q qNum.
Proof.
ir. ap qNat_qNum. ap in_qNat_qNat.
am.
Qed.

Lemma qOpp_qNat_qRel : forall q, inc q qNum -> inc (qOpp q) qNat -> inc q qRel.
Proof.
ir.
cp (qOpp_qOpp H).
wr H1. ap union2_r. ap Im_inc. am.
Qed.

Lemma qNat_pos : forall q, inc q qNat -> qLeq q0 q.
Proof.
ir. apply Z_all in H. ee.
nin H0.
qSolve.
apply qLeq_trans with (qPlus q0 q1);qSolve.
rw qPlus_0_l;qSolve.
ap in_qNat_qNum.
am.
ap qLeq_qPlus_compat;qSolve.
ap in_qNat_qNum;am.
ap IHin_qNat.
ap in_qNat_qNum;am.
Qed.

Lemma qRel_pos_qNat : forall q, inc q qRel -> qLeq q0 q -> inc q qNat.
Proof.
ir. apply union2_or in H;nin H.
am.
Im_nin H;subst.
cp (qNat_pos H).
cp (qNat_qNum H).
rwi qLeq_qOpp H1;qSolve. rwi qOpp_q0 H1.
replace (qOpp x) with q0. ap in_qNat_qNat. constructor.
ap qLeq_antisym;qSolve.
Qed.

Lemma qRel_qOpp_stable : forall q, inc q qRel -> inc (qOpp q) qRel.
Proof.
ir. apply union2_or in H;nin H;[ap union2_r | ap union2_l].
ap Im_inc;am.
Im_nin H;subst. cp (qNat_qNum H).
rw (qOpp_qOpp H0);qSolve.
Qed.

Lemma qNat_q0 : inc q0 qNat.
Proof.
ap in_qNat_qNat. constructor.
Qed.

Lemma qRel_q0 : inc q0 qRel.
Proof.
ap qNat_qRel. ap qNat_q0.
Qed.

Lemma qNat_q1 : inc q1 qNat.
Proof.
wr (qPlus_0_l q1_inc).
ap in_qNat_qNat. constructor. constructor.
Qed.

Lemma qRel_q1 : inc q1 qRel.
Proof.
ap qNat_qRel;ap qNat_q1.
Qed.

Lemma qNat_S : forall q, inc q qNat -> inc (qPlus q q1) qNat.
Proof.
ir. ap in_qNat_qNat. constructor. eapply Z_pr. am.
Qed.

Lemma zPos_qNat : forall z, inc z zPos -> inc [J z z1] qNat.
Proof.
ir. cp H. apply zPos_in_zPos in H. nin H.
ap qNat_q0.
cp (in_zPos_zPos H).
cp (IHin_zPos H1). clear IHin_zPos.
wr qPlus_same_denom;zSolve.
ap qNat_S. am.
ap (Z_sub H1).
Qed.

Lemma qNum_frac0 : forall q, inc q qNum = exists a, exists b, 
inc a zNum & inc b zNum & z0<>b & q = qMult [J a z1] (qInv [J b z1]).
Proof.
ir;ap iff_eq;ir.
rwi qNum_rw H. nin H;nin H;ee.
subst. exists x;exists x0;ee;zSolve.
rw qInv_rw;zSolve. rw qMult_passes;zSolve.
rw zMult_1_r;zSolve. rw zMult_1_l;zSolve.
nin H;nin H;ee;subst.
qSolve;try ap qNum_inc;zSolve.
uhg;ir. apply q0_eq_pr in H2. subst. au.
zSolve. zSolve.
zSolve.
Qed.

Lemma zNum_qRel : forall z, inc z zNum -> inc [J z z1] qRel.
Proof.
ir.
cp H.
apply zNum_disj in H;nin H.
ap qNat_qRel. ap zPos_qNat. am.
wr (zOpp_zOpp H0).
wr qOpp_rw;zSolve.
ap qRel_qOpp_stable.
ap qNat_qRel. ap zPos_qNat.
am.
Qed.

Lemma qNat_zPos : forall q, inc q qNat -> exists z, inc z zPos & q = [J z z1].
Proof.
ir. apply Z_all in H;ee. nin H0.
exists z0;ee;zSolve. uf zPos. ap Z_inc;zSolve.
cp (in_qNat_qNum H0).
cp (IHin_qNat H1). clear IHin_qNat.
nin H2. ee;subst.
exists (zPlus x z1);ee.
ap in_zPos_zPos. constructor. ap zPos_in_zPos. am.
cp (Z_sub H2).
uf q1. rw qPlus_same_denom;zSolve.
Qed.

Lemma qRel_zNum : forall q, inc q qRel -> exists z, inc z zNum & q = [J z z1].
Proof.
ir. apply union2_or in H;nin H.
apply qNat_zPos in H. nin H. exists x;ee.
apply (Z_sub H).
am.
Im_nin H.
apply qNat_zPos in H. nin H. ee. subst.
cp (Z_sub H).
exists (zOpp x0);ee.
zSolve.
ap qOpp_rw;zSolve.
Qed.

Lemma qNum_frac : forall q, inc q qNum = exists q1, exists q2, 
inc q1 qRel & inc q2 qRel & q2 <> q0 & q = qMult q1 (qInv q2).
Proof.
ir;ap iff_eq;ir.
rwi qNum_frac0 H. nin H;nin H;ee;subst.
econstructor;econstructor;ee.
Focus 4. reflexivity.
ap zNum_qRel. am.
ap zNum_qRel. am.
uhg;ir. apply q0_eq_pr in H2;zSolve.
au.
nin H;nin H;ee;subst.
qSolve;ap qRel_qNum;am.
Qed.

(*after this point we should not need zNum anymore*)

Definition qTimes n q := pow qPlus q0 q n.

Lemma qTimes_0 : forall q, qTimes n0 q = q0.
Proof.
ap pow_0.
Qed.

Lemma qTimes_S : forall n, inc n nNum ->
 forall q, qTimes (oS n) q = qPlus q (qTimes n q).
Proof.
ir. ap pow_S. am.
Qed.

Definition qTimes_end :
forall x : E,
       (x ∈ qNum) ->
       forall n : E,
       (n ∈ ω) -> qTimes (oS n) x = qPlus (qTimes n x) x
:= pow_atend qPlus_monoid.

Lemma qTimes_1 : forall x, inc x qNum -> qTimes n1 x = x.
Proof.
ap pow_1. ap qPlus_monoid.
Qed.

Lemma qTimes_qNat : forall n, inc n nNum -> inc (qTimes n q1) qNat.
Proof.
ap nNum_rect.
rw qTimes_0. ap qNat_q0.
ir. rw qTimes_end. ap in_qNat_qNat. constructor.
eapply Z_pr;am.
qSolve.
am.
Qed.

Lemma qNat_qTimes : forall q, inc q qNat -> exists n, inc n nNum & q = qTimes n q1.
Proof.
ir. apply Z_all in H. ee.
nin H0.
exists n0;ee. nSolveS.
rw qTimes_0. tv.
cp (in_qNat_qNum H0).
cp (IHin_qNat H1). clear IHin_qNat.
nin H2;ee;subst.
exists (oS x).
ee. nSolveS.
symmetry. ap qTimes_end. qSolve.
am.
Qed.

Definition qOpp_qPlus : forall x y : E,
       (x ∈ qNum) ->
       (y ∈ qNum) ->
       qOpp (qPlus x y) =
       qPlus (qOpp y) (qOpp x)
:= group_inverse_of_law qPlus_group.

Lemma qTimes_inc : forall n, inc n nNum -> forall q, inc q qNum ->
 inc (qTimes n q) qNum.
Proof.
pose (p n := forall q, inc q qNum -> inc (qTimes n q) qNum).
assert (forall n, inc n nNum -> p n);try am.
ap nNum_rect;uf p;clear p;ir.
rw qTimes_0. qSolve.
rw qTimes_S;qSolve.
ap H0. am.
Qed.

Lemma qOpp_qTimes : forall n, inc n nNum -> forall q, inc q qNum -> 
qOpp (qTimes n q) = qTimes n (qOpp q).
Proof.
pose (p n := forall q : E, (q ∈ qNum) -> qOpp (qTimes n q) = qTimes n (qOpp q)).
assert (forall n, inc n nNum -> p n);try am.
ap nNum_rect;uf p;clear p;ir.
rw qTimes_0. rw qTimes_0. ap qOpp_q0.
cp (H0 q H1).
rw qTimes_S. rw qTimes_S.
rw qOpp_qPlus;qSolve;try ap qTimes_inc;qSolve.
rw qPlus_comm;qSolve;try ap qTimes_inc;qSolve.
ap uneq. am. am. am.
Qed.

Lemma qTimes_distrib : forall x, inc x qNum -> forall y, inc y qNum -> 
forall n, inc n nNum -> qTimes n (qPlus x y) = qPlus (qTimes n x) (qTimes n y).
Proof.
intros x Hx y Hy. ap nNum_rect;ir.
repeat rw qTimes_0. symmetry. ap qPlus_0_l;qSolve.
repeat rw qTimes_S;try am.
rw H0.
cp (qTimes_inc H Hx).
cp (qTimes_inc H Hy).
wr qPlus_assoc. wr qPlus_assoc.
ap uneq. rw qPlus_comm. wr qPlus_assoc. ap uneq. ap qPlus_comm.
am. am. am. am. am.
am. qSolve. am. am. qSolve. am. am. qSolve.
Qed.

Lemma qTimes_plus : forall q, inc q qNum -> forall n, inc n nNum -> 
forall m, inc m nNum -> qTimes (nPlus n m) q = qPlus (qTimes n q) (qTimes m q).
Proof.
ap pow_nPlus. ap qPlus_monoid.
Qed.

Lemma qTimes_qMult : forall q, inc q qNum -> forall n, inc n nNum -> 
qTimes n q = qMult (qTimes n q1) q.
Proof.
intros q Hq. ap nNum_rect;ir.
rw qTimes_0. rw qTimes_0. symmetry. ap qMult_0_l. am.
repeat rw qTimes_S;nSolveS.
rw H0.
cp (qTimes_inc H Hq).
cp (qTimes_inc H q1_inc).
rw qMult_distrib_r;qSolve.
rw qMult_1_l;qSolve.
Qed.

Lemma qInv_qOpp : forall q, inc q qNum -> q<>q0 -> 
qInv (qOpp q) = qOpp (qInv q).
Proof.
ir.
eapply Lci.inverse_unicity.
ap qMult_monoid.
ap Lci.inversible_inverse_of.
ap qMult_monoid.
ap qNum_field. qSolve.
uhg;ir. ap H0.
wr (qOpp_qOpp H). rw H1. ap qOpp_q0.
uhg. ee;qSolve.
wr qOpp_qMult_r. wr qOpp_qMult_l.
rw qOpp_qOpp. ap qInv_r. qSolve. qSolve.
qSolve. qSolve. qSolve. qSolve. qSolve.
wr qOpp_qMult_r. wr qOpp_qMult_l.
rw qOpp_qOpp. ap qInv_l. qSolve. qSolve.
qSolve. qSolve. qSolve. qSolve. qSolve.
Qed.

Lemma qNum_frac_proper : forall q, inc q qNum -> exists num, exists denom, 
inc num qRel & inc denom qNat & denom <> q0 & q = qMult num (qInv denom).
Proof.
ir. rwi qNum_frac H. nin H;nin H;ee;subst.
apply union2_or in H0;nin H0.
exists x;exists x0;ee;au.
Im_nin H0;subst.
exists (qOpp x). exists x1.
ee. ap qRel_qOpp_stable. am.
am.
uhg;ir. subst. ap H1. ap qOpp_q0.
cp (qRel_qNum H).
cp (qNat_qNum H0).
rw qInv_qOpp.
wr qOpp_qMult_l. symmetry. ap qOpp_qMult_r.
am. qSolve. uhg;ir;subst. ap H1. ap qOpp_q0.
am. qSolve. uhg;ir;subst;ap H1;ap qOpp_q0.
am. uhg;ir;subst;ap H1;ap qOpp_q0.
Qed.

Lemma qInv_pos : forall q, inc q qNum -> q <> q0 -> qLeq q0 q -> qLeq q0 (qInv q).
Proof.
ir.
rw (leq_not_lt (conj qLeq_order qLeq_total));qSolve.
uhg;ir. nin H2.
assert (Lci.inversible qMult qNum q1 q). ap qNum_field. am. am.
apply inversible_inverse_of in H4.
uh H4;ee.
ap q0_q1_neq.
ap qLeq_antisym;qSolve.
fold qInv in H6. clear H7.
wr H6.
rw qLeq_qOpp;qSolve. rw qOpp_q0.
rw qOpp_qMult_r;qSolve.
ap qNum_ofield;qSolve.
rw qLeq_qOpp;qSolve. rw qOpp_qOpp;qSolve.
rw qOpp_q0. am.
ap qMult_monoid.
Qed.

Lemma qTimes_order : forall q, inc q qNum -> qLeq q0 q -> q<>q0 -> 
forall n, inc n nNum -> forall m, inc m nNum -> 
nLeq n m -> qLeq (qTimes n q) (qTimes m q).
Proof.
intros q Hq H H0.
intros n Hn.
assert (forall k, inc k nNum -> qLeq (qTimes n q) (qTimes (nPlus n k) q)).
ap nNum_rect;ir.
rw nPlus_0. qSolve. ap qTimes_inc. am. am. am.
rw nPlus_S;try am. rw qTimes_S;qSolve.
cp (qTimes_inc Hn Hq).
wr (qPlus_0_l H3). ap qLeq_qPlus_compat;qSolve.
ap qTimes_inc;qSolve.
ir. rwi nLeq_rw H3;nSolveS. nin H3;ee;subst;au.
Qed.

Lemma qTimes_reg_l : forall q, inc q qNum -> q <> q0 -> forall n, inc n nNum -> 
forall m, inc m nNum -> qTimes n q = qTimes m q -> n=m.
Proof.
intros q Hq H.
pose (p n := forall m : E, (m ∈ ω) -> qTimes n q = qTimes m q -> n = m).
assert (forall n, inc n nNum -> p n);try am.
ap nNum_rect;uf p;clear p.
pose (p m := qTimes ∅ q = qTimes m q -> ∅ = m).
assert (forall m, inc m nNum -> p m);try am.
ap nNum_rect;uf p;clear p;ir.
tv.
ap False_rect. rwi qTimes_0 H2.
rwi qTimes_S H2.
destruct (qLeq_total q0_inc Hq).
assert (qLeq q0 (qTimes n q)).
wr (qTimes_0 q). ap qTimes_order.
am. am. am. nSolveS. am. nSolveS.
rwi (leq_not_lt (conj qLeq_order qLeq_total)) H3;qSolve.
ap H3. uhg;ee. rw qLeq_qOpp;qSolve. rw qOpp_q0.
replace (qOpp q) with (qTimes n q).
am.
cp (qTimes_inc H0 Hq).
apply qPlus_reg_l with q;qSolve.
rw qOpp_r;qSolve. symmetry. am.
am.
cp (qTimes_inc H0 Hq).
assert (qLeq (qTimes n q) q0).
rw qLeq_qOpp;qSolve. rw qOpp_q0.
rw qOpp_qTimes;qSolve. 
wr (qTimes_0 (qOpp q)). ap qTimes_order;qSolve.
rw qLeq_qOpp;qSolve. rw qOpp_qOpp. rw qOpp_q0. am.
am. uhg;ir.
ap H. wr (qOpp_qOpp Hq). rw H5. ap qOpp_q0.
nSolveS.
rwi (leq_not_lt (conj qLeq_order qLeq_total)) H3;qSolve.
ap H3. uhg;ee.
replace q with (qOpp (qTimes n q)).
rw qLeq_qOpp;qSolve. rw qOpp_qOpp;qSolve.
rw qOpp_q0. am.
apply qPlus_reg_r with (qTimes n q);qSolve. rw qOpp_l;qSolve.
uhg;ir;subst.
au.
am.
intros n Hn IH.

pose (p m := qTimes (oS n) q = qTimes m q -> oS n = m).
assert (forall m, inc m nNum -> p m);au.
ap nNum_rect;uf p;clear p;ir.
ap False_rect.
rwi qTimes_0 H0. rwi qTimes_S H0;qSolve.
cp (qTimes_inc Hn Hq).
assert (qTimes n q = qOpp q).
apply qPlus_reg_l with q;qSolve.
rw qOpp_r;qSolve.
destruct (qLeq_total Hq q0_inc).
assert (qLeq (qTimes n q) q0).
rw qLeq_qOpp;qSolve. rw qOpp_qTimes;qSolve. rw qOpp_q0.
wr (qTimes_0 (qOpp q)). ap qTimes_order;qSolve.
rw qLeq_qOpp;qSolve. rw qOpp_qOpp;qSolve;rw qOpp_q0.
am.
uhg;ir. ap H. apply qPlus_reg_l with (qOpp q);qSolve.
rw qOpp_l;qSolve. rw qPlus_0_r;qSolve. au.
nSolveS.
rwi (leq_not_lt (conj qLeq_order qLeq_total)) H3;qSolve.
ap H3;uhg;ee.
wr (qOpp_qOpp Hq). wr H2. wr qOpp_q0.
wr qLeq_qOpp;qSolve. uhg;ir;ap H;au.
assert (qLeq q0 (qTimes n q)).
wr (qTimes_0 q). ap qTimes_order;qSolve.
nSolveS.
rwi (leq_not_lt (conj qLeq_order qLeq_total)) H3;qSolve. ap H3;uhg;ee.
rw qLeq_qOpp;qSolve. rw qOpp_q0;wr H2. am.
uhg;ir;au.

ap uneq.
rwi qTimes_S H2;qSolve. rwi qTimes_S H2;qSolve.
apply qPlus_reg_l in H2;qSolve.
apply IH in H2. am. am. ap qTimes_inc;am.
ap qTimes_inc;am.
Qed.

Lemma qTimes_reg_r : forall n, inc n nNum -> n<>n0 ->
forall q, inc q qNum -> forall q', inc q' qNum -> 
qTimes n q = qTimes n q' -> q=q'.
Proof.
ir.
rwi qTimes_qMult H3;qSolve.
rwi (qTimes_qMult (q := q')) H3;qSolve.
cp (qTimes_inc H q1_inc). set (qn := qTimes n q1) in *.
assert (qMult qn (qPlus q (qOpp q')) = q0).
rw qMult_distrib_l;qSolve. wr qOpp_qMult_r;qSolve.
rw H3. ap qOpp_r;qSolve.
apply qMult_integral in H5;qSolve. nin H5.
ufi qn H5.
nin H0.
apply qTimes_reg_l with q1. qSolve. qSolve. am. nSolveS.
rw qTimes_0. am.
apply qPlus_reg_r with (qOpp q');qSolve. rw H5. symmetry.
ap qOpp_r;qSolve.
Qed.

Lemma archi_aux : forall q, inc q qNum -> exists n, inc n nNum & qLeq q (qTimes n q1).
Proof.
ir. destruct (qLeq_total H q0_inc).
exists n0. ee. nSolveS.
rw qTimes_0. am.
apply qNum_frac_proper in H.
destruct H as [p H];destruct H as [d H];ee;subst.
cp (qNat_qNum H1);cp (qRel_qNum H).
cp (qNat_pos H1).
assert (qLeq q0 p).
rw (leq_not_lt (conj qLeq_order qLeq_total));qSolve.
uhg;ir. nin H6.
assert (qMult p (qInv d) = q0).
ap qLeq_antisym;qSolve.
rw qLeq_qOpp;qSolve.
rw qOpp_q0. rw qOpp_qMult_l;qSolve.
ap qNum_ofield;qSolve.
rw qLeq_qOpp;qSolve. rw qOpp_qOpp;qSolve. rw qOpp_q0;am.
ap qInv_pos. qSolve. am. am.
apply qMult_integral in H8;qSolve.
nin H8;au. apply qInv_neq in H8. am.
am. am.
cp (qRel_pos_qNat H H6).
cp (qNat_qTimes H1).
cp (qNat_qTimes H7).
destruct H8 as [a H8]. destruct H9 as [b H9].
ee;subst.
assert (a <> n0).
uhg;ir;subst;ap H2. ap qTimes_0.
exists b;ee. am.
apply qLeq_trans with (qMult (qTimes b q1) q1);qSolve.
apply qLeq_qPlus_reg_r with (qOpp (qMult (qTimes b q1) q1));qSolve.
rw qOpp_r;qSolve.
rw qOpp_qMult_r;qSolve.
wr qMult_distrib_l;qSolve.
rw qLeq_qOpp;qSolve.
 rw qOpp_q0.
rw qOpp_qMult_r.
ap qNum_ofield. qSolve. wr (qTimes_0 q1). ap qTimes_order.
qSolve. qSolve. qSolve. nSolveS. am. nSolveS.
qSolve.
rw qOpp_qPlus;qSolve.
rw qOpp_qOpp;qSolve.
apply qLeq_qPlus_reg_l with (qOpp q1);qSolve.
rw qPlus_0_r;qSolve. rw qPlus_assoc;qSolve.
rw qOpp_l;qSolve. rw qPlus_0_l;qSolve.
wr qLeq_qOpp;qSolve.
assert (qLeq q0 (qTimes a q1)).
ap qNat_pos. ap qTimes_qNat. am.
apply qLeq_qMult_reg_l with (qTimes a q1);qSolve.
rw qInv_r;qSolve. rw qMult_1_r;qSolve.
assert (qLeq (qTimes n1 q1) (qTimes a q1)).
ap qTimes_order;qSolve.
uf n1. apply nNum_destruct in H8. nin H8.
nin H10;ap H8.
nin H8;ee;subst.
wr nLeq_S_S;nSolveS.
ufi n1 H12. rwi qTimes_S H12. rwi qTimes_0 H12.
rwi qPlus_0_r H12;qSolve. nSolveS.
am. qSolve.
rw qMult_1_r;qSolve.
Qed.

Lemma qNum_archimedean : forall x, inc x qNum -> x<>q0 -> qLeq q0 x ->
forall y, inc y qNum -> exists n, inc n nNum & qLeq  y (qTimes n x).
Proof.
ir.
assert (inc (qMult y (qInv x)) qNum). qSolve.
apply archi_aux in H3.
nin H3;ee.
exists x0. ee. am.
rw qTimes_qMult;qSolve.
apply qLeq_qMult_reg_l with (qInv x);qSolve.
ap qInv_neq;qSolve.
ap qInv_pos;qSolve.
ap qTimes_inc;qSolve.
rw qMult_comm;qSolve.
replace (qMult (qInv x) (qMult (qTimes x0 q1) x))
with (qMult (qMult (qTimes x0 q1) x) (qInv x)).
cp (qTimes_inc H3 q1_inc).
wr qMult_assoc;qSolve.
rw qInv_r;qSolve. rw qMult_1_r;qSolve.
ap qMult_comm;qSolve.
ap qTimes_inc;qSolve.
Qed.

Lemma qMult_qTimes : forall n, inc n nNum -> forall m, inc m nNum -> 
forall q, inc q qNum -> forall q', inc q' qNum -> 
qMult (qTimes n q) (qTimes m q') = qMult (qTimes (nMult n m) q1) (qMult q q').
Proof.
pose (p n := 
forall m : E,
(m ∈ ω) ->
forall q : E,
(q ∈ qNum) ->
forall q' : E,
(q' ∈ qNum) ->
qMult (qTimes n q) (qTimes m q') = qMult (qTimes (nMult n m) q1) (qMult q q')).
assert (forall n, inc n nNum -> p n);try am.
ap nNum_rect;uf p;clear p.
ir.
rw qTimes_0. rw nMult_0_l.  rw qTimes_0. rw qMult_0_l.
rw qMult_0_l;qSolve.
ap qTimes_inc;am.

intros n Hn IH.
ir.
rw qTimes_S;try am.
rw nMult_S_l;nSolveS.
rw qTimes_plus;nSolveS;qSolve.
rw qMult_distrib_r;try am.
rw IH;try am.
rw qMult_distrib_r.
wr qTimes_qMult.
ap uneq2.
rw qMult_comm;qSolve. rw (qMult_comm H0);qSolve.
rw qMult_assoc. wr qTimes_qMult. tv. am. am.
ap qTimes_inc;qSolve.
am. am. ap qTimes_inc;qSolve.
tv. qSolve. nSolveS. ap qTimes_inc;qSolve.
ap qTimes_inc;qSolve. qSolve. ap qTimes_inc;am.
ap qTimes_inc;am.
Qed.

End NotaSec.

End QFrac.
