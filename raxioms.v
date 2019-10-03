
Set Implicit Arguments.
Unset Strict Implicit.

Require Export nnum_base.
Require Import aac.
Require Export quotient.

Module CAxioms.
Export Ordered_ring.

Parameter cNum :  E.
Parameter rNum : E.

Axiom rNum_sub_cNum : sub rNum cNum.
Axiom nNum_sub_rNum : sub nNum rNum.

Definition nNum_sub_cNum := sub_trans nNum_sub_rNum rNum_sub_cNum.

Notation ℕ := nNum.
Notation ℝ := rNum.
Notation ℂ := cNum.

Lemma r0_inc : inc n0 rNum.
Proof.
ap nNum_sub_rNum. nSolveS.
Qed.

Lemma c0_inc : inc n0 cNum.
Proof.
ap nNum_sub_cNum. nSolveS.
Qed.

Lemma r1_inc : inc n1 rNum.
Proof.
ap nNum_sub_rNum. nSolveS.
Qed.

Lemma c1_inc : inc n1 cNum.
Proof.
ap nNum_sub_cNum. nSolveS.
Qed.

Parameters (cPlus cMult : E2).
Parameter (I : E).

Axiom I_inc : inc I cNum.

Axiom cNum_field : is_field cPlus cMult cNum n0 n1.

Axiom rNum_field : is_field cPlus cMult rNum n0 n1.

Axiom cMult_comm : commutative cMult cNum.

Axiom cPlus_nPlus : forall x, inc x nNum -> forall y, inc y nNum -> cPlus x y = nPlus x y.
Axiom cMult_nMult : forall x, inc x nNum -> forall y, inc y nNum -> cMult x y = nMult x y.

Parameter rLeq : E2P.

Axiom rLeq_to : is_total_order rLeq rNum.

Axiom rNum_ordered_field : is_ordered_field cPlus cMult rLeq rNum n0 n1.

Axiom rLeq_nLeq : forall x, inc x nNum -> forall y, inc y nNum -> rLeq x y = nLeq x y.

Axiom rNum_ex_sup : forall a, sub a rNum -> nonempty a -> ex (is_upper_bound rNum rLeq a) -> 
ex (is_super rNum rLeq a).

Definition cOpp := Lci.inverse_of cPlus cNum n0.

Axiom I_2 : cMult I I = cOpp n1.

Axiom complex_parts_unicity : forall a, inc a rNum -> forall b, inc b rNum -> 
forall a', inc a' rNum -> forall b', inc b' rNum -> cPlus a (cMult I b) = cPlus a' (cMult I b') -> 
(a=a' & b=b').





End CAxioms.
Export CAxioms.




