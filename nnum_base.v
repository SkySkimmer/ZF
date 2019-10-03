
Set Implicit Arguments.
Unset Strict Implicit.

Require Export ordinal_arith.

Module nNum_ring. (*actually quasiring but too long to bother*)
Export Ordinal. Export Cardinal.
Import Ordinal_arith.
Import Cardinal_arith.
Export Ordered_lci.

Definition nPlus := caPlus.
Definition nMult := caMult.
Definition nLeq := sub.
Definition n0 := emptyset.
Definition n1 := oS emptyset.

Lemma nPlus_oPlus : forall x, inc x nNum -> forall y, inc y nNum -> 
nPlus x y = oPlus x y.
Proof.
intros x Hx. ap nNum_rect;uf nPlus;ir.
rw caPlus_N_0_r. rw oPlus_0_r. tv. am.
rw caPlus_N_S. rw oPlus_S. ap uneq. am.
apply nNum_ordinal;am. am. am.
Qed.

Lemma nMult_oMult : forall x, inc x nNum -> forall y, inc y nNum -> 
nMult x y = oMult x y.
Proof.
uf nMult;intros x Hx;ap nNum_rect;ir.
rw caMult_0_r. rw oMult_0_r. tv.
rw caMult_N_S. rw oMult_S. wr H0.
wr nPlus_oPlus. tv. ap caMult_N_lci.
am. am. am. apply nNum_ordinal;am.
am. am.
Qed.

Lemma nPlus_0 : forall x, inc x nNum -> nPlus x n0 = x.
Proof.
ir. uf n0. uf nPlus. ap caPlus_N_0_r. am.
Qed.

Lemma nPlus_comm : forall x y, nPlus x y = nPlus y x.
Proof.
uf nPlus. ap caPlus_comm.
Qed.

Lemma nMult_comm : forall x y, nMult x y = nMult y x.
Proof.
uf nMult;ap caMult_comm.
Qed.

Lemma nPlus_assoc : forall x y z, nPlus x (nPlus y z) = nPlus (nPlus x y) z.
Proof.
uf nPlus;ap caPlus_assoc.
Qed.

Lemma nMult_assoc : forall x y z, nMult x (nMult y z) = nMult (nMult x y) z.
Proof.
ap caMult_assoc.
Qed.

Lemma nMult_distrib_r : forall x y z, nMult (nPlus x y) z = nPlus (nMult x z) (nMult y z).
Proof.
ir;ap caMult_distrib_r.
Qed.

Lemma nMult_distrib_l : forall x y z, nMult x (nPlus y z) = nPlus (nMult x y) (nMult x z).
Proof.
ir. ap caMult_distrib_l.
Qed.

Lemma nPlus_0_l : forall x, inc x nNum -> nPlus n0 x = x.
Proof.
ir. rw nPlus_comm. ap nPlus_0. am.
Qed.

Lemma nMult_0 : forall x, nMult x n0 = n0.
Proof.
ir. uf nMult. rw caMult_0_r. tv.
Qed.

Lemma nMult_0_l : forall x, nMult n0 x = n0.
Proof.
ir;rw nMult_comm;ap nMult_0.
Qed.

Lemma nPlus_S : forall x, inc x nNum -> forall y, inc y nNum -> 
nPlus x (oS y) = oS (nPlus x y).
Proof.
uf nPlus. ap caPlus_N_S.
Qed.

Lemma nMult_S : forall x, inc x nNum -> forall y, inc y nNum -> 
nMult x (oS y) = nPlus (nMult x y) x.
Proof.
uf nPlus;uf nMult;ap caMult_N_S.
Qed.

Lemma nPlus_S_l : forall x, inc x nNum -> forall y, inc y nNum -> 
nPlus (oS x) y = oS (nPlus x y).
Proof.
ir.
rw nPlus_comm. rw nPlus_S. ap uneq. ap nPlus_comm.
am. am.
Qed.

Lemma nMult_S_l : forall x, inc x nNum -> forall y, inc y nNum -> 
nMult (oS x) y = nPlus y (nMult x y).
Proof.
ir. rw nMult_comm. rw nMult_S;au.
rw nMult_comm;ap nPlus_comm.
Qed.

Lemma n0_inc : inc n0 nNum.
Proof.
ap emptyset_N.
Qed.

Lemma n1_inc : inc n1 nNum.
Proof.
ap oS_nNum. ap emptyset_N.
Qed.

Lemma nPlus_lci : is_lci nPlus nNum.
Proof.
uf nPlus;ap caPlus_N_lci.
Qed.

Lemma nMult_lci : is_lci nMult nNum.
Proof.
ap caMult_N_lci.
Qed.

Ltac nSolveS := match goal with 
  | |- inc n0 nNum => exact (n0_inc)
  | |- inc emptyset nNum => exact (n0_inc)
  | |- inc n1 nNum => exact (n1_inc)
  | |- inc (oS emptyset) nNum => exact (n1_inc)
  | |- inc (oS _) nNum => ap oS_nNum;nSolveS
  | |- inc (nPlus _ _) nNum => ap nPlus_lci;nSolveS
  | |- inc (nMult _ _) nNum => ap nMult_lci;nSolveS
  | |- inc _ nNum => try am
  | |- nLeq emptyset _ => ap emptyset_sub_all
  | |- nLeq n0 _ => ap emptyset_sub_all
  | |- nLeq ?x ?x => ap sub_refl
  | |- nLeq ?x (oS ?x) => ap oS_sub
  | |- sub n0 _ => ap emptyset_sub_all
  | |- sub emptyset _ => ap emptyset_sub_all
  | |- sub ?x ?x => ap sub_refl
  | |- sub ?x (oS ?x) => ap oS_sub
  | _ => try tv
  end.

Lemma nMult_1 : forall x, inc x nNum -> nMult x n1 = x.
Proof.
ir. uf n1;rw nMult_S;nSolveS.
rw nMult_0. rw nPlus_0_l;nSolveS.
Qed.

Lemma nMult_1_l : forall x, inc x nNum -> nMult n1 x = x.
Proof.
ir;rw nMult_comm;ap nMult_1;am.
Qed.

Lemma oS_emptyset_neq : forall x, oS x <> emptyset.
Proof.
uhg;ir. apply emptyset_empty with x;wr H;rw oS_inc;au.
Qed.

Lemma nMult_pow : forall x, inc x nNum -> forall y, inc y nNum -> 
nMult x y = Pow.pow nPlus n0 x y.
Proof.
intros x Hx;ap nNum_rect;ir.
rw nMult_0. symmetry. ap nNum_repeat_0.
rw nMult_S;nSolveS.
rw Pow.pow_S. wr H0.
ap nPlus_comm. am.
Qed.

Lemma nPlus_n0_neutre : is_neutre nPlus nNum n0.
Proof.
uhg;ee;nSolveS. ap nPlus_0. ap nPlus_0_l.
Qed.

Lemma nMult_n1_neutre : is_neutre nMult nNum n1.
Proof.
uhg;ee. nSolveS.
ap nMult_1. ap nMult_1_l.
Qed.

Lemma nPlus_N_assoc : associative nPlus nNum.
Proof.
uhg;ir;ap nPlus_assoc.
Qed.

Lemma nMult_N_assoc : associative nMult nNum.
Proof.
uhg;ir;ap nMult_assoc.
Qed.

Lemma nPlus_monoid : is_monoid nPlus nNum n0.
Proof.
ap caPlus_N_monoid.
Qed.

Lemma nMult_monoid : is_monoid nMult nNum n1.
Proof.
ap caMult_N_monoid.
Qed.

Lemma nPlus_reg_r : is_reg_r nPlus nNum.
Proof.
uhg.
assert (forall y y', inc y nNum -> inc y' nNum -> forall x, inc x nNum -> 
nPlus y x = nPlus y' x -> y=y').
intros y y' Hy Hy'. pose (p := fun x => nPlus y x = nPlus y' x -> y=y').
assert (forall x, inc x nNum -> p x);try am.
ap nNum_rect;uf p;ir.
rwi nPlus_0 H;nSolveS. rwi nPlus_0 H;nSolveS.
rwi nPlus_S H1;nSolveS. rwi nPlus_S H1;nSolveS.
apply oS_N_inj in H1;nSolveS. au.
ir;eau.
Qed.

Lemma nPlus_reg_l : is_reg_l nPlus nNum.
Proof.
uhg;ir;eapply nPlus_reg_r.
ap H. am. am.
rw nPlus_comm. rw H2. ap nPlus_comm.
Qed.

Lemma nPlus_reg : is_regular nPlus nNum.
Proof.
uhg;ee. ap nPlus_reg_l. ap nPlus_reg_r.
Qed.

Lemma nPlus_le_l : forall a, inc a nNum -> forall b, sub a (nPlus a b).
Proof.
ir. apply sub_trans with (card a).
rw nNum_card. ap sub_refl. am.
ap iso_sub_card_sub.
rw iso_sub_rw. exists (L a (fun x => J emptyset x)).
ap map_of_injective.
uhg;ee;uhg;ir. ap union2_l.
ap product_pair_inc. ap singleton_inc.
am.
apply pair_eq in H2;ee;am.
Qed.

Lemma nPlus_le_r : forall a, inc a nNum -> forall b, sub a (nPlus b a).
Proof.
ir. rw nPlus_comm. ap nPlus_le_l;am.
Qed.

Lemma nPlus_0eq : forall a b, nPlus a b = n0 -> (a=n0 & b=n0).
Proof.
ap caPlus_0eq.
Qed.

Lemma nMult_integral_all : forall x y, nMult x y = n0 -> (x=n0 \/ y=n0).
Proof.
ap caMult_integral.
Qed.

Lemma nMult_integral : is_integral nMult nNum n0.
Proof.
uhg;ir;ap nMult_integral_all;am.
Qed.

Lemma nMult_distributes : distributes nPlus nMult nNum.
Proof.
ap caMult_N_distrib.
Qed.

Lemma nPlus_N_comm : commutative nPlus nNum.
Proof.
uhg;ir;ap nPlus_comm.
Qed.

Lemma nMult_N_comm : commutative nMult nNum.
Proof.
uhg;ir;ap nMult_comm.
Qed.

Lemma nNum_quasiring : is_quasiring nPlus nMult nNum n0 n1.
Proof.
ap ca_N_quasiring.
Qed.

Lemma nMult_1eq : forall x, inc x nNum -> forall y, inc y nNum -> 
nMult x y = n1 -> (x=n1 & y=n1).
Proof.
uf n1;ir.
apply nNum_destruct in H0. nin H0;subst.
rwi nMult_0 H1. edestruct oS_emptyset_neq.
symmetry;am.
ap PropGuard_use.
nin H0;ee;subst.

apply nNum_destruct in H;nin H;subst.
rwi nMult_0_l H1;nSolveS.  edestruct oS_emptyset_neq.
symmetry;am.
nin H;ee;subst.
rwi nMult_S H1;nSolveS. rwi nPlus_S H1;nSolveS.
apply oS_N_inj in H1;nSolveS.
apply nPlus_0eq in H1.
ee;subst.
rwi nMult_comm  H1. rwi nMult_S H1;nSolveS.
rwi nMult_0 H1. rwi nPlus_0_l H1;nSolveS.
subst. constructor. ee;tv.
Qed.

Lemma nLeq_rw : forall x, inc x nNum -> forall y, inc y nNum -> 
nLeq x y = (exists z, inc z nNum & y = nPlus x z).
Proof.
ir. etransitivity.
uf nLeq. ap iff_eq. ap ordinal_sub_ex;ap nNum_ordinal;am.
ir. nin H1;ee. subst.
ap oPlus_sub_l. ap nNum_ordinal;am.
am.

ap iff_eq;ir;nin H1;ee;subst.
exists x0;dj.
cp (nNum_ordinal H).
rw ordinal_inc_not_sub;au.
uhg;ir. assert (sub x0 (oPlus x x0)).
ap oPlus_sub_r. am. am.
cp (sub_trans H3 H4).
assert (sub (oPlus x x0) nNum). ap omega_ordinal.
am. cp (extensionality H5 H6).
wri H7 H0. eapply omega_ordinal. ap H0.
am. ap omega_ordinal.
symmetry. ap nPlus_oPlus. am. am.
exists x0;ee;au. ap nNum_ordinal;am.
ap nPlus_oPlus;am.
Qed.

Definition nLt := lt_of nLeq.

Lemma nLt_inc_rw : forall x, inc x nNum -> forall y, inc y nNum -> 
nLt x y = inc x y.
Proof.
ir. uf nLt. uf nLeq. ap ordinal_inc_lt_of;ap nNum_ordinal;am. 
Qed.

Lemma inc_nLt : forall x, inc x nNum -> forall y, inc y x -> nLt y x.
Proof.
ir. assert (inc y nNum).
cp (and_P omega_ordinal). eapply H1. am. am.
rw nLt_inc_rw;au.
Qed.

Lemma nLt_S : forall x y, inc y nNum -> nLeq (oS x) y -> nLt x y.
Proof.
ir. ap inc_nLt. am. ap H0. rw oS_inc;au.
Qed.

Lemma nLt_S_rw : forall x, inc x nNum -> forall y, inc y nNum -> 
nLt x y = nLeq (oS x) y.
Proof.
ir. rw nLt_inc_rw;au. ap iff_eq;ir.
cp (inc_nLt H0 H1).
nin H2. uhg;uhg;ir. rwi oS_inc H4;nin H4;au. subst.
am. ap H1. rw oS_inc;au.
Qed.

Lemma nLeq_wo : is_well_order nLeq nNum.
Proof.
ap ordinal_sub_wo. ap omega_ordinal.
Qed.

Lemma nLeq_to : is_total_order nLeq nNum.
Proof.
ap well_order_total_order. ap nLeq_wo.
Qed.

Lemma nLeq_total : is_total nLeq nNum.
Proof.
ap well_order_total. ap nLeq_wo.
Qed.

Lemma nLeq_S_S : forall x, inc x nNum -> forall y, inc y nNum -> 
nLeq x y = nLeq (oS x) (oS y).
Proof.
ir;ap iff_eq;ir.
uhg;uhg;ir.
rwi oS_inc H2;nin H2;rw oS_inc;au. subst.
uh H1. rwi ordinal_sub_leq_of H1. am.
ap nNum_ordinal;am. ap nNum_ordinal;am.
ufi nLeq H1. uf nLeq.
destruct (nLeq_total H H0).
am.
uh H2. apply by_cases with (inc y (oS x));ir.
assert (x=y);subst;nSolveS.
ap oS_N_inj;au. ap extensionality. am.
fold nLeq. wr nLt_S_rw;nSolveS. uhg;uhg;ee.
uhg;uhg;ir;rw oS_inc;au.
ap ordinal_inc_neq;au. ap nNum_ordinal;nSolveS.
apply sub_trans with (oS x).
nSolveS.
uhg;ir. cp (H1 a H4).
rwi oS_inc H5;nin H5. am.
subst. nin H3;am.
Qed.

Lemma nLt_S_S : forall x, inc x nNum -> forall y, inc y nNum -> 
nLt x y = nLt (oS x) (oS y).
Proof.
ir. rw nLt_S_rw;nSolveS. rw nLt_S_rw;nSolveS.
ap nLeq_S_S;nSolveS.
Qed.

Lemma nLeq_nPlus_compat : is_compatible nLeq nPlus nNum.
Proof.
ap invariant_compat. ap sub_is_order.
ap nPlus_lci.
uhg. dj.
uhg;ir.
rwi nLeq_rw H2;au. nin H2;ee;subst.
rw nLeq_rw;nSolveS.
exists x0;ee. am.
wr nPlus_assoc. rw (nPlus_comm x0). rw nPlus_assoc.
tv.

uhg;ir. rw nPlus_comm. rw (nPlus_comm x).
ap H;am.
Qed.

Lemma nPlus_ordered_monoid : is_ordered_monoid nLeq nPlus nNum n0.
Proof.
uhg;ee. ap sub_is_order. ap nPlus_monoid.
ap nLeq_nPlus_compat.
Qed.

Lemma nLeq_nMult_compat : is_compatible nLeq nMult nNum.
Proof.
ap invariant_compat. ap sub_is_order.
ap nMult_lci.
uhg. dj;uhg;ir.
rwi nLeq_rw H2;nSolveS;rw nLeq_rw;nSolveS.
nin H2;ee;subst.
rw nMult_distrib_r.
exists (nMult x0 x).
ee;nSolveS.
rw nMult_comm. rw (nMult_comm x). ap H;am.
Qed.

Lemma nMult_reg_l : forall x, inc x nNum -> x<>emptyset -> 
forall a, inc a nNum -> forall b, inc b nNum -> 
nMult x a = nMult x b -> 
a=b.
Proof.
pose (p := fun a => forall x, inc x nNum -> forall b, inc b nNum -> 
nMult (oS x) a = nMult (oS x) b -> a=b).
assert (forall a, inc a nNum -> p a).
ap nNum_rect;uf p;clear p;ir.
rwi nMult_0 H1. symmetry in H1. apply nMult_integral in H1;nSolveS.
nin H1;subst;au. edestruct oS_emptyset_neq. am.

apply nNum_destruct in H2;nin H2;subst.
rwi nMult_0 H3. apply nMult_integral in H3;nSolveS.
nin H3;edestruct oS_emptyset_neq;am.
nin H2;ee;subst.
rwi nMult_S H3;nSolveS.
rwi nMult_S H3;nSolveS.
apply nPlus_reg_r in H3;nSolveS.
ap uneq. eau.

ufi p H;clear p.
ir. apply nNum_destruct in H0;nin H0;subst. nin H1;tv.
nin H0;ee;subst.
eau.
Qed.

Lemma nMult_reg_r : forall x, inc x nNum -> x<>emptyset -> 
forall a, inc a nNum -> forall b, inc b nNum -> 
nMult a x = nMult b x -> 
a=b.
Proof.
ir. eapply nMult_reg_l.
ap H. am. am. am.
rw nMult_comm;rw H3. ap nMult_comm.
Qed.

Lemma nLt_nLeq_trans : forall x y, nLt x y -> forall z, nLeq y z -> nLt x z.
Proof.
ap subLt_sub_trans.
Qed.

Lemma nLeq_nLt_trans : forall x y, nLeq x y -> forall z, nLt y z -> nLt x z.
Proof.
ap sub_subLt_trans.
Qed.

Lemma nLt_trans : forall x y, nLt x y -> forall z, nLt y z -> nLt x z.
Proof.
intros x y H. ap nLeq_nLt_trans. am.
Qed.

Lemma nLeq_nPlus_reg_r : forall x, inc x nNum -> 
forall a, inc a nNum -> forall b, inc b nNum -> 
nLeq (nPlus a x) (nPlus b x) -> nLeq a b.
Proof.
ir. rw nLeq_rw;nSolveS. rwi nLeq_rw H2;nSolveS.
nin H2;ee;subst.
exists x0. ee. am.
apply nPlus_reg_r with x. am. am. nSolveS.
rw H3. repeat wr nPlus_assoc.
ap uneq. ap nPlus_comm.
Qed.

Lemma nLeq_nPlus_reg_l : forall x, inc x nNum -> 
forall a, inc a nNum -> forall b, inc b nNum -> 
nLeq (nPlus x a) (nPlus x b) -> nLeq a b.
Proof.
intros x Hx a Ha b Hb.
rw nPlus_comm. rw (nPlus_comm x). ap nLeq_nPlus_reg_r;am.
Qed.

Lemma nLeq_nMult_reg_l : forall a, inc a nNum -> a<>n0 -> 
forall x, inc x nNum -> forall y, inc y nNum -> nLeq (nMult a x) (nMult a y) -> 
nLeq x y.
Proof.
ir.
rw (leq_not_lt nLeq_to);try am.
uhg;ir. nin H4.
assert (nMult a x = nMult a y).
ap extensionality;fold nLeq;try am.
ap nLeq_nMult_compat;try am.
ap sub_refl.
ap H5. apply nMult_reg_l with a.
am. am. am. am. au.
Qed.

Lemma nLeq_nMult_reg_r : forall a, inc a nNum -> a<>n0 -> 
forall x, inc x nNum -> forall y, inc y nNum -> nLeq (nMult x a) (nMult y a) -> 
nLeq x y.
Proof.
ir. apply nLeq_nMult_reg_l with a;try am.
rw nMult_comm. rw (nMult_comm a). am.
Qed.

End nNum_ring.

Module Pow_nNum.
Export Pow. Export nNum_ring.
Import Ordinal. (*for omega*)

Section VarSec.

Variables (law : E2) (g e : E).

Hypothesis (Hmon : is_monoid law g e).

Notation Pow := (pow law e).

Lemma pow_are_inverse : forall x y, Lci.are_inverse law g e x y -> forall n, inc n nNum -> 
Lci.are_inverse law g e (Pow x n) (Pow y n).
Proof.
intros x y H. ap nNum_rect.
rw pow_0. rw pow_0.
uhg;ee. am. am.
ap Hmon;am. ap Hmon;am.

ir.
uhg;ee. 
ap pow_inc. am. am. ap oS_nNum;am.
ap pow_inc. am. am. ap oS_nNum;am.
erewrite pow_atend;try am.
rw pow_S;try am.
transitivity (law (Pow x n) (law (law x y) (Pow y n))).
assert (is_lci law g);try am.
assert (associative law g);try am.
uh H;ee;uh H1;ee.
repeat rw H3;au.
uh H;ee. rw H3.
assert (is_neutre law g e);try am.
uh H5;ee. rw H7;am.

erewrite pow_atend;try am.
rw pow_S;try am.
transitivity (law (Pow y n) (law (law y x) (Pow x n))).
assert (is_lci law g);try am.
assert (associative law g);try am.
uh H;ee;uh H1;ee.
repeat rw H3;au.
uh H;ee. rw H4.
assert (is_neutre law g e);try am.
uh H5;ee. rw H7;am.
Qed.

Lemma pow_inversible_inverse : forall x, inversible law g e x -> 
forall n, inc n nNum -> inverse_of law g e (Pow x n) = Pow (inverse_of law g e x) n.
Proof.
ir.
nin H. assert (x0 = inverse_of law g e x).
eapply Lci.inverse_unicity. am. am. ap inversible_inverse_of.
am. exists x0;am.
wr H1.
cp (pow_are_inverse H H0).
eapply Lci.inverse_unicity. am. Focus 2. am.
ap inversible_inverse_of. am. econstructor;am.
Qed.

Lemma pow_nPlus : forall x, inc x g -> 
forall n, inc n nNum -> forall m, inc m nNum -> 
Pow x (nPlus n m) = law (Pow x n) (Pow x m).
Proof.
intros x Hx n Hn.
cp (pow_inc Hmon).
ap nNum_rect;ir.
rw nPlus_0;try am. rw pow_0. symmetry. ap Hmon.
ap pow_inc. am. am. am.
rw nPlus_S;try am.
symmetry.
rw pow_S;nSolveS.
assert (associative law g). am.
rw H2;au. wr (pow_atend Hmon);try am.
rw pow_S;au. wr H2;au.
wr H1. symmetry. ap pow_S.
nSolveS.
Qed.

Lemma pow_nPlus_inverse : forall x y, Lci.are_inverse law g e x y -> 
forall n, inc n nNum -> forall m, inc m nNum -> law (Pow x (nPlus n m)) (Pow y m) = Pow x n.
Proof.
ir.
cp H. uh H2;ee.
rw pow_nPlus;nSolveS.
cp (pow_inc Hmon).
cp (and_Q (and_Q Hmon)).
wr H7;au.
cp (pow_are_inverse H H1).
uh H8;ee. rw H10.
ap Hmon;au.
Qed.

End VarSec.

(*needs to be out to not require is_monoid*)
Lemma pow_group_inverse : forall law g e, is_group law g e -> 
forall x, inc x g -> forall n, inc n nNum -> inverse_of law g e (pow law e x n) = pow law e (inverse_of law g e x) n.
Proof.
intros law g e Hgr x Hx. ap pow_inversible_inverse. ap group_is_monoid;am.
ap Hgr;am.
Qed.

End Pow_nNum.
Export Pow_nNum.


