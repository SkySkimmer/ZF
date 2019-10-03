
Set Implicit Arguments.
Unset Strict Implicit.

Require Export lci.

Module Ring.

Section Laws.

Variables (pl ml : E2).

Definition distrib_l g := (forall a, inc a g -> forall b, inc b g -> forall c, inc c g -> 
  ml c (pl a b) = pl (ml c a) (ml c b)).

Definition distrib_r g :=(forall a, inc a g -> forall b, inc b g -> forall c, inc c g -> 
ml (pl a b) c = pl (ml a c) (ml b c)).

Definition distributes g := A (distrib_l g) (distrib_r g).

Definition is_ring g e u := 
A (is_group pl g e)
(A (commutative pl g)
(A (is_monoid ml g u)
(distributes g))).


Definition is_quasiring a e u :=
A (is_monoid pl a e)
(A (is_monoid ml a u)
(A (distributes a)
(A (forall x, inc x a -> ml e x = e)
(forall x, inc x a -> ml x e = e)))).


Lemma ring_0_multr : forall g e u, is_ring g e u -> 
forall x, inc x (g) -> ml x e = e.
Proof.
ir. uh H;ee.
uh H;uh H2;uh H3;ee.
assert (is_regular pl g). apply group_is_regular with e. uhg;ee;am.
uh H10;ee.
apply H10 with (ml x e);au.
ap H2;am.
ap H2;am.
wr H3;au. uh H6;ee. rw H12;au.
rw H12;au.
Qed.

Lemma ring_0_multl : forall g e u, is_ring g e u -> 
forall x, inc x (g) -> ml e x = e.
Proof.
ir. uh H;ee.
uh H;uh H2;uh H3;ee.
assert (is_regular pl g). apply group_is_regular with e. uhg;ee;am.
uh H10;ee.
apply H10 with (ml e x);au.
ap H2;am.
ap H2;am.
wr H4;au. uh H6;ee. rw H12;au.
rw H12;au.
Qed.

Lemma ring_is_quasiring : forall g e u, is_ring g e u -> is_quasiring g e u.
Proof.
ir;uhg;ee;try am.
ap group_is_monoid;am.
eapply ring_0_multl. am. 
eapply ring_0_multr. am. 
Qed.

Definition is_integral g e := forall a, inc a (g) -> forall b, inc b (g) -> 
ml a b = e -> (a=e \/ b=e).

Lemma integral_rw : forall g e u, is_ring g e u -> is_integral g e -> 
forall a b, inc a (g) -> inc b (g) -> 
(ml a b = e) = ((a=e)\/(b=e)).
Proof.
ir. ap iff_eq;ir.
ap H0. am. am. am.

nin H3;subst.
apply ring_0_multl with g u. am. am.
apply ring_0_multr with g u;am.
Qed.

Lemma minus_u_multl : forall g e u, is_ring g e u -> forall x, inc x (g) -> 
ml (inverse_of pl g e u) x = inverse_of pl g e x.
Proof.
ir.
assert (are_inverse pl g e x (inverse_of pl g e x)). ap group_inverse_of. am. am.
uh H1;ee. assert (is_regular pl g). apply group_is_regular with e;am.
uh H5;ee.
apply H6 with x. am. uh H;ee. uh H8;ee. ap H8. ap group_inverse_inc. am.
am. am. ap group_inverse_inc. am. am.
rw H4.
replace (pl (ml (inverse_of pl g e u) x) x) with (pl (ml (inverse_of pl g e u) x) (ml u x)).
uh H;ee. uh H9;ee.
wr H10. assert (are_inverse pl g e u (inverse_of pl g e u)). ap group_inverse_of.
am. am. uh H11;ee. rw H14. apply ring_0_multl with g u. uhg;ee. am. am. am. uhg;ee;am.
am. ap group_inverse_inc;am. am. am. uh H;ee. uh H8;ee.
uh H10;ee. rw H13. tv. am.
Qed.

Lemma minus_u_multr : forall g e u, is_ring g e u -> forall x, inc x (g) -> 
ml x (inverse_of pl g e u) = inverse_of pl g e x.
Proof.
ir.
assert (are_inverse pl g e x (inverse_of pl g e x)). ap group_inverse_of. am. am.
uh H1;ee. assert (is_regular pl g). apply group_is_regular with e;am.
uh H5;ee.
apply H6 with x. am. uh H;ee. uh H8;ee. ap H8. am. ap group_inverse_inc. am.
am. am.
rw H4.
replace (pl (ml x (inverse_of pl g e u)) x) with (pl (ml x (inverse_of pl g e u)) (ml x u)).
uh H;ee. uh H9;ee.
wr H9. assert (are_inverse pl g e u (inverse_of pl g e u)). ap group_inverse_of.
am. am. uh H11;ee. rw H14. apply ring_0_multr with g u. uhg;ee. am. am. am. uhg;ee;am.
am. ap group_inverse_inc;am. am. am. uh H;ee. uh H8;ee.
uh H10;ee. rw H12. tv. am.
Qed.

Lemma inverse_ml_insert_left : forall g e u, is_ring g e u -> 
forall a b, inc a g -> inc b g ->
inverse_of pl g e (ml a b) = ml (inverse_of pl g e a) b.
Proof.
ir. eapply inverse_unicity.
ap group_is_monoid. am.
ap group_inverse_of. am. uh H;ee. uh H3;ee. au.
erewrite <-minus_u_multl.
Focus 2. ap H.
uh H;ee. uh H3;ee.
wr H6;au. rw minus_u_multl;au.
ap group_inverse_of. am. au.
uhg;ee; au. uhg;ee;am.
ap group_inverse_inc;am. am.
Qed.

Lemma inverse_ml_insert_right : forall g e u, is_ring g e u -> 
forall a b, inc a g -> inc b g ->
inverse_of pl g e (ml a b) = ml a (inverse_of pl g e b).
Proof.
ir. eapply inverse_unicity.
ap group_is_monoid. am.
ap group_inverse_of. am. uh H;ee. uh H3;ee. au.
erewrite <-minus_u_multr.
Focus 2. ap H.
uh H;ee. uh H3;ee.
rw H6;au. rw minus_u_multr;au.
ap group_inverse_of. am. au.
uhg;ee; au. uhg;ee;am.
ap group_inverse_inc;am. am.
Qed.

Lemma integral_quasiregular_left : forall g e u, is_ring g e u -> is_integral g e -> 
forall a b c, inc a g -> inc b g -> inc c g -> a<>e ->
ml a b = ml a c -> b = c.
Proof.
ir.
assert (are_inverse pl g e (ml a b) (inverse_of pl g e (ml a c))).
rw H5. ap group_inverse_of. am. uh H;ee. uh H7;ee;au.
uh H6;ee.
uh H;ee. uh H12;ee.
erewrite inverse_ml_insert_right in H8. Focus 2.
uhg;ee. am. am. ap H11. uhg;ee;am.
wri H12 H8;au.
uh H0;ee. apply H0 in H8. nin H8.
ap False_rect. au.
assert (is_regular pl g). eapply group_is_regular;am.
uh H14;ee. apply H15 with (inverse_of pl g e c).
ap group_inverse_inc;am. am. am.
rw H8. assert (are_inverse pl g e c (inverse_of pl g e c)). ap group_inverse_of;am.
symmetry;am. am.
uh H;ee;ap H. am. ap group_inverse_inc;au. uhg;ee;am.
ap group_inverse_inc;am. am. am.
Qed.

Lemma integral_quasiregular_right : forall g e u, is_ring g e u -> is_integral g e -> 
forall a b c, inc a g -> inc b g -> inc c g -> a<>e ->
ml b a = ml c a -> b = c.
Proof.
ir.
assert (are_inverse pl g e (ml b a) (inverse_of pl g e (ml c a))).
rw H5. ap group_inverse_of. am. uh H;ee. uh H7;ee;au.
uh H6;ee.
uh H;ee. uh H12;ee.
erewrite inverse_ml_insert_left in H9. Focus 2.
uhg;ee. am. am. ap H11. uhg;ee;am.
wri H13 H9;au.
uh H0;ee. apply H0 in H9. nin H9.
assert (is_regular pl g). eapply group_is_regular;am.
uh H14;ee. apply H14 with (inverse_of pl g e c).
ap group_inverse_inc;am. am. am.
rw H9. assert (are_inverse pl g e c (inverse_of pl g e c)). ap group_inverse_of;am.
symmetry;am.
ap False_rect;au.
uh H;ee;ap H;au. ap group_inverse_inc;au. uhg;ee;am. am.
ap group_inverse_inc;am. am. am.
Qed.

Lemma integral_injective_l : forall g e u, is_ring g e u -> is_integral g e -> 
forall a, inc a g -> a<>e -> Application.injective g g (ml a).
Proof.
ir;uhg;ee;uhg;ir.
ap H. am. am.
eapply integral_quasiregular_left. am. am.
ap H1. am. am. am. am.
Qed.

Lemma integral_injective_r : forall g e u, is_ring g e u -> is_integral g e -> 
forall a, inc a g -> a<>e -> Application.injective g g (fun x => ml x a).
Proof.
ir;uhg;ee;uhg;ir.
ap H. am. am.
eapply integral_quasiregular_right. am. am.
ap H1. am. am. am. am.
Qed.

End Laws.

End Ring. Export Ring.

Module Ideal.

Section Law.

Variables (pl ml : E2) (a e u : E).
Hypothesis (rgH : is_ring pl ml a e u).

Definition is_ideal b := 
A (is_subgroup pl a e b)
(A (forall x, inc x (b) -> forall y, inc y (a) -> inc (ml x y) (b))
(forall x, inc x (b) -> forall y, inc y (a) -> inc (ml y x) (b))).

Definition ideal_of x := Im (fun z => ml x z) a.

Definition is_principal_ideal b := is_ideal b & (exists x, inc x (a) & b = ideal_of x).

Definition is_principal_ring := forall b, is_ideal b -> is_principal_ideal b.

Lemma ideal_of_ideal : commutative ml a -> 
forall x, inc x (a) ->
is_principal_ideal (ideal_of x).
Proof.
ir. uhg. ee.
uhg;ee.
ap subgroup_show. am.
uf ideal_of. uhg;ir. apply Im_ex in H1;nin H1;ee;subst.
ap rgH;am.
exists e. ap Im_show_inc. exists e. ee. ap rgH.
symmetry;eapply ring_0_multr. ap rgH. am.

ir. ufi ideal_of H1;apply Im_ex in H1;nin H1;ee;subst.
ufi ideal_of H2;apply Im_ex in H2;nin H2;ee;subst.
cp rgH. uh H3;ee. uh H6;ee. wr H6;au.
ap Im_inc. ap H3. am. am.

ir. ufi ideal_of H1;apply Im_ex in H1;nin H1;ee;subst.
erewrite inverse_ml_insert_right. Focus 2. ap rgH.
ap Im_inc. ap group_inverse_inc;am.
am. am.

Focus 3. exists x. ee;au.

ir. ufi ideal_of H1;apply Im_ex in H1;nin H1;ee;subst.
cp rgH. uh H3;ee. uh H5;ee. wr H8;au.
ap Im_inc;au.

ir.
ufi ideal_of H1;apply Im_ex in H1;nin H1;ee;subst.
cp rgH. uh H3;ee. uh H5;ee. rw H8;au.
replace (ml y x) with (ml x y);au. 
wr H8;au. ap Im_inc;au.
Qed.

Lemma principal_is_ideal : forall b, is_principal_ideal b -> is_ideal b.
Proof.
ir. uh H. nin H;ee. am.
Qed.

End Law.


Section Division.

Variables (pl ml : E2) (a e u : E).
Hypotheses (rgH : is_ring pl ml a e u)
(comH : commutative ml a).

Definition divides x y := exists z, inc z (a) & y = ml x z.

Lemma divide_ideal_rw : forall x y, inc x (a) -> inc y (a) -> 
divides x y = (sub (ideal_of ml a y) (ideal_of ml a x)).
Proof.
ir. ap iff_eq;ir.
nin H1;ee. subst.
uhg;ir. ufi ideal_of H2;apply Im_ex in H2;nin H2;ee;subst.
cp rgH.
uh H3;ee. uh H5;ee. wr H8;au.

ap Im_inc. au.

uhg.
assert (inc y (ideal_of ml a y)).
ap Im_show_inc. exists u. ee. am.
symmetry;ap rgH. am. apply H1 in H2. apply Im_ex in H2. nin H2;ee;subst.
exists x0;ee;au.
Qed.

Lemma divides_refl : forall x, inc x a -> divides x x.
Proof.
ir. uhg.
exists u;ee. am.
symmetry. ap rgH. am.
Qed.

Lemma divides_transitiveT : forall x y z, inc x (a) -> inc y (a) -> inc z (a) -> 
divides x y -> divides y z -> divides x z.
Proof.
ir. rw divide_ideal_rw;au. rwi divide_ideal_rw H3;rwi divide_ideal_rw H2;au.
uhg;ir;au.
Qed.

End Division.


End Ideal.

Module SubRing.

Section Law.

Variables (pl ml : E2).

Definition is_subring a e u b :=
A (sub (b) (a))
(is_ring pl ml b e u).

Lemma subring_subgroup : forall a e u b, is_subring a e u b -> is_subgroup pl a e b.
Proof.
ir. uhg. ee. am. am.
Qed.

Lemma show_ring_by_subring : forall b e u, (exists a, is_subring a e u b) -> is_ring pl ml b e u.
Proof.
ir. nin H. am.
Qed.

Lemma show_subring : forall a e u b, is_ring pl ml a e u -> 
is_subgroup pl a e b -> 
inc u (b) -> 
(forall x, inc x b -> forall y, inc y b -> inc (ml x y) b) -> 
is_subring a e u b.
Proof.
ir. assert (sub b a). am.
uhg;ee. am.
uhg. ee. am.
uhg;ir. ap H. au. au.
uh H;ee. 
uhg;ee. am.
uhg;ee. am.
ir. ap H5. au.
ir. ap H5;au.

uhg;ir. ap H5;au.

uhg; ee;uhg;ir.
ap H;au. ap H;au.
Qed.

End Law.

End SubRing. Export SubRing.

Module Field.

Definition is_field pl ml a e u := 
A (is_ring pl ml a e u)
(forall x, inc x a -> x<>e -> inversible ml a u x).

Lemma field_integral : forall pl ml a e u, is_field pl ml a e u ->
is_integral ml a e. ir.
Proof.
uhg. ir.
apply by_cases with (a0 = e);ir.
left;am.
cp H3. apply H in H3.
nin H3;uh H3;ee.
assert (x<>e). uhg;ir.
rwi H8 H7. uh H;ee. cp H. rwi (ring_0_multl H) H7.
ap H4. uh H10;ee. uh H12;ee. uh H14;ee. symmetry. wr H16.
wr H7. symmetry. eapply ring_0_multr. ap H.
am. am. am.
assert (b = ml x e).
wr H2. uh H;ee. uh H;ee.
uh H11;ee. rw H14;try am. rw H7. symmetry.
ap H13;am.
right. rw H9. eapply ring_0_multr. ap H. am. am.
Qed.

Lemma field_mult_quasireg_l : forall pl ml g e u, is_field pl ml g e u ->
forall a b c, inc a g -> inc b g -> inc c g -> a<>e ->
ml a b = ml a c -> b = c.
Proof.
ir. eapply integral_quasiregular_left. ap H. eapply field_integral.
ap H. ap H0. am. am. am. am.
Qed.

Lemma field_mult_quasireg_r : forall pl ml g e u, is_field pl ml g e u ->
forall a b c, inc a g -> inc b g -> inc c g -> a<>e ->
ml b a = ml c a -> b = c.
Proof.
ir. eapply integral_quasiregular_right. ap H. eapply field_integral.
ap H. ap H0. am. am. am. am.
Qed.

Lemma field_mult_group : forall pl ml a e u, is_field pl ml a e u -> e<>u -> 
is_group ml (Z a (fun x => x <> e)) u.
Proof.
ir.
assert (is_lci ml (Z a (fun x : E => x <> e))).
uhg;ir. Ztac;au. Ztac;au.
ap Z_inc. ap H;am.
uhg;ir. apply (field_integral H) in H5;try am.
nin H5;au.
uhg;ee. am.
uhg;ee. ap Z_inc. am. uhg;ir;au.
ir. Ztac;au.
ap H. am.
ir. ap H. Ztac;au. 
uhg;ir. Ztac;au;Ztac;au;Ztac;au.
ap H;am.
ir.
Ztac;au. uh H;ee. cp (H4 x H2 H3).
nin H5.
exists x0.
uhg;ee. ap Z_inc;am.
ap Z_inc. am. uhg;ir;subst.
uh H5;ee. rwi (ring_0_multr H) H7. ap H0;am.
am.
am. am.
Qed.

Lemma field_inverse_of : forall pl ml a e u, is_field pl ml a e u -> 
forall x, inc x (Z a (fun x => x<>e)) -> 
are_inverse ml (Z a (fun x => x<>e)) u x (inverse_of ml a u x).
Proof.
ir. Ztac;au.
uh H;ee. cp (H2 x H0 H1).
apply inversible_inverse_of in H3.
uhg;ee;try am.
ap Z_inc;am. ap Z_inc. am.
uhg;ir;uh H3;ee.
rwi H4 H7. rwi (ring_0_multl H) H7;try am.
ap H1. replace x with (ml u x). wr H7.
ap (ring_0_multl H). am.
ap H. am.
am.
Qed.

End Field. Export Field.

(*
Module Fraction_field.
Export Quotient.

Section Law.

Variables (pl ml : E2) (r e u : E).

Hypotheses (rgH : is_ring pl ml r e u) (iH : is_integral ml r e) (cH : commutative ml r).
Hypothesis (uH : u<>e).

Definition qEquiv x y := ml (P x) (Q y) = ml (P y) (Q x).

Lemma qEquiv_zEquiv : qEquiv = Group_of_Monoid.zEquiv ml.
Proof.
uf Group_of_Monoid.zEquiv. ap arrow_extensionality;ir.
ap arrow_extensionality;ir. uf qEquiv. tv.
Qed.

Definition qBase := product r (Z r (fun x => x <> e)).

Lemma qEquiv_equivalence : is_equivalence qBase qEquiv.
Proof.
uhg;ee.
ir. uf qEquiv. tv.
ir. uhg. uh H1. symmetry. am.
ir. uh H2;uh H3.
uhg.
apply product_pr in H;ee. clear H;Ztac;clear H5.
apply product_pr in H0;ee. clear H0;Ztac;clear H7.
apply product_pr in H1;ee. clear H1;Ztac;clear H9.

cp (integral_quasiregular_right rgH iH).
apply H9 with (Q y).
am. ap rgH;am. ap rgH;am.
am.
assert (is_lci ml r). am.
rw cH;au. cp rgH. uh H12;ee. clear H11;clear H12;clear H13;clear H15.
uh H14. ee. rw H13;try am.
rwi cH H2;try am. rw H2.
symmetry. symmetry in H3.
rw cH;au. rw H13;try am.
rwi cH H3;try am. rw H3.
symmetry. rw cH;au. rw H13;try am.
rw (cH H1 H5). tv.
Qed.

Definition qF := quotient qBase qEquiv.

Definition qMl0 x y := J (ml (P x) (P y)) (ml (Q x) (Q y)).

Lemma qMl0_lci : is_lci qMl0 qBase.
Proof.
uhg;ir.
uf qMl0. apply product_pr in H;apply product_pr in H0.
ap product_pair_inc. ap rgH. am. am.
ee. Ztac;clear H2;Ztac;clear H4.
ap Z_inc. ap rgH;am.
uhg;ir. apply iH in H4. nin H4;au. am. am.
Qed.

Lemma qMl0_compat : forall a b, inc a r -> inc b r -> b<>e -> 
forall a' b', inc a' r -> inc b' r -> b'<>e -> 
qEquiv (J a b) (J a' b') -> 
forall c d, inc c r -> inc d r -> d<>e -> 
forall c' d', inc c' r -> inc d' r -> d'<>e -> 
qEquiv (J c d) (J c' d') -> 
qEquiv (qMl0 (J a b) (J c d)) (qMl0 (J a' b') (J c' d')).
Proof.
uf qEquiv;uf qMl0;ir.
clear_pr. clear_pr_in H12. clear_pr_in H5.

transitivity (ml (ml a b') (ml c d')).
assert (forall f:E1, forall x y, x=y -> f x = f y). ir. rw H13;tv.
assert (is_lci ml r). am. assert (associative ml r). am.
wr H15;au. symmetry. wr H15;au. ap H13.
rw cH;au. wr H15;au.

rw H5. rw H12.
assert (forall f:E1, forall x y, x=y -> f x = f y). ir. rw H13;tv.
assert (is_lci ml r). am. assert (associative ml r). am.
wr H15;au. symmetry. wr H15;au. ap H13.
rw cH;au. wr H15;au.
Qed.

Lemma qMl0_compat0 : forall a, inc a qBase -> forall a', inc a' qBase -> qEquiv a a' -> 
forall b, inc b qBase -> forall b', inc b' qBase -> qEquiv b b' -> 
qEquiv (qMl0 a b) (qMl0 a' b').
Proof.
ir.
apply product_pr in H;apply product_pr in H0;apply product_pr in H2;apply product_pr in H3;ee.
apply pair_recov in H;apply pair_recov in H0;apply pair_recov in H2;apply pair_recov in H3.
wr H;wr H0;wr H2;wr H3.
ap qMl0_compat;try am.
eapply Z_sub. am. apply Z_pr in H12;am.
eapply Z_sub. am. apply Z_pr in H10;am.
uhg. clear_pr. am.
eapply Z_sub. am. apply Z_pr in H8;am.
eapply Z_sub. am. apply Z_pr in H6;am.
uhg;clear_pr;am.
Qed.

Notation "[ x ]" := (class_of qBase qEquiv x).

Definition qMl x y := [ qMl0 (rep x) (rep y) ].

Lemma qMl_lci : is_lci qMl qF.
Proof.
uhg;ir.
uf qF;uf qMl;uf qMl0.
cp (in_quotient_is_class H). cp (in_quotient_is_class H0).
ap class_of_in_quotient.
ap qMl0_lci. assert (sub x qBase).
uh H1;ee. uh H1;ee. am.
ap H3. eapply class_rep_inc. ap H1.
assert (sub y qBase).
uh H2;ee. uh H2;ee. am.
ap H3. eapply class_rep_inc. ap H2.
Qed.

Lemma qMl_rep_rw0 : forall x y, inc x qBase -> inc y qBase -> 
qMl [x] [y] = [ qMl0 x y ].
Proof.
ir. uf qMl.
ap related_classes_eq. ap qMl0_lci.
cp (class_sub (class_of_class qEquiv H)).
ap H1. eapply class_rep_inc. ap class_of_class. am.
cp (class_sub (class_of_class qEquiv H0)).
ap H1. eapply class_rep_inc. ap class_of_class. am.
ap qMl0_lci;am.
ap qMl0_compat0.
cp (class_sub (class_of_class qEquiv H)).
ap H1. eapply class_rep_inc. ap class_of_class. am.
am.
eapply equivalent_related.
ap qEquiv_equivalence.
uhg. ee.
cp (class_sub (class_of_class qEquiv H)).
ap H1. eapply class_rep_inc. ap class_of_class. am.
am.
ap class_of_rep. ap class_of_in_quotient. am.
cp (class_sub (class_of_class qEquiv H0)).
ap H1. eapply class_rep_inc. ap class_of_class. am.
am.
eapply equivalent_related.
ap qEquiv_equivalence.
uhg. ee.
cp (class_sub (class_of_class qEquiv H0)).
ap H1. eapply class_rep_inc. ap class_of_class. am.
am. ap class_of_rep.
ap class_of_in_quotient. am.
Qed.

Lemma qMl_rep_rw : forall a b, inc a r -> inc b r -> b<>e -> 
forall c d, inc c r -> inc d r -> d<>e -> 
qMl [J a b] [J c d] = [J (ml a c) (ml b d)].
Proof.
ir. rw qMl_rep_rw0. uf qMl0. clear_pr.
tv. ap product_pair_inc. am. ap Z_inc;am.
ap product_pair_inc. am. ap Z_inc;am.
Qed.

Definition qU := [ J u u ].

Lemma qU_inc : inc qU qF.
Proof.
ap class_of_in_quotient. ap product_pair_inc.
am. ap Z_inc. am. am.
Qed.

Lemma qMl_comm : commutative qMl qF.
Proof.
uhg;ir.
cp (class_of_rep H). cp (class_of_rep H0).
assert (inc (rep x) qBase).
eapply class_sub. ap in_quotient_is_class. ap H.
eapply class_rep_inc. ap in_quotient_is_class. ap H.
assert (inc (rep y) qBase).
eapply class_sub. ap in_quotient_is_class. ap H0.
eapply class_rep_inc. ap in_quotient_is_class. ap H0.

apply product_pr in H3;apply product_pr in H4;ee.
uf qMl. uf qMl0.
Ztac;clear H6;Ztac;clear H8.
rw (cH H7 H5). rw (cH H6 H9). tv.
Qed.

Lemma qRep_inc : forall x, inc x qF -> inc (rep x) qBase.
Proof.
ir.
eapply class_sub. ap in_quotient_is_class. ap H.
eapply class_rep_inc. ap in_quotient_is_class. ap H.
Qed.

Lemma qF_mult_monoid : is_monoid qMl qF qU.
Proof.
uhg;ee. ap qMl_lci.
uhg. assert (forall x : E, inc x qF -> qMl x qU = x).
ir. uf qU.
assert (inc (rep x) qBase).
eapply class_sub. ap in_quotient_is_class. ap H.
eapply class_rep_inc. ap in_quotient_is_class. ap H.
apply product_pr in H0;ee.
Ztac;clear H2.
assert ([rep x] = x). ap class_of_rep. am.
wr H2. rw qMl_rep_rw0.
uf qMl0. clear_pr.
cp rgH. uh H5;ee. uh H7;ee.
uh H9;ee. rw H11. rw H11. rw pair_recov. tv.
am. am. am. ap product_inc;try am. ap Z_inc;am.
ap product_pair_inc. am. ap Z_inc;am.
ee;try am.
ap qU_inc.
ir. rw qMl_comm. ap H. am.
ap qU_inc. am.

uhg;ir.
cp (class_of_rep H). cp (class_of_rep H0). cp (class_of_rep H1).
cp (qRep_inc H);cp (qRep_inc H0);cp (qRep_inc H1).
replace (qMl y z) with ([ qMl0 (rep y) (rep z)]).
replace (qMl x y) with ([ qMl0 (rep x) (rep y)]).
wr H2. rw qMl_rep_rw0.
rw H2. wr H4. rw qMl_rep_rw0.
rw H4.
uf qMl0. clear_pr.
apply product_pr in H5;ee;apply product_pr in H6;ee;apply product_pr in H7;ee.
Ztac;clear H13;Ztac;clear H11;Ztac;clear H9.
assert (is_lci ml r). am. assert (associative ml r). am.
rw H18;au. rw H18;au.
ap qMl0_lci;am. am. am. ap qMl0_lci;am.
uf qMl. tv. uf qMl. tv.
Qed.

Definition qE := [J e u].

Lemma qE_inc : inc qE qF.
Proof.
ap class_of_in_quotient. ap product_pair_inc.
am. ap Z_inc;am.
Qed.

Lemma qF_mult_inversible0 : forall a b, inc (J a b) qBase -> [J a b] <> qE -> 
inversible qMl qF qU [J a b].
Proof.
ir.
exists [J b a].
apply product_pair_pr in H;ee;Ztac. clear H1.
uhg.
assert (aH : a<>e).
uhg;ir;subst. ap H0.
ap related_classes_eq. ap product_pair_inc.
am. ap Z_inc;am.
ap product_pair_inc.
am. ap Z_inc;am.
uhg;clear_pr.
rw (ring_0_multl rgH);try am. rw (ring_0_multl rgH);try am.
tv.

assert (preH : qMl [J a b] [J b a] = qU).
rw qMl_rep_rw.
rw cH;try am.
uf qU. ap related_classes_eq.
ap product_pair_inc. ap rgH;am.
ap Z_inc. ap rgH;am. uhg;ir.
apply iH in H1. nin H1;au.
am. am. ap product_pair_inc. am. ap Z_inc;am.
uhg;clear_pr.
assert (is_neutre ml r u). am.
uh H1;ee. rw H4;au. rw H5;au.
ap rgH;am. ap rgH;am.
am. am. am. am. am. am.

ee. ap class_of_in_quotient. ap product_pair_inc. am.
ap Z_inc;am.
ap class_of_in_quotient;ap product_pair_inc.
am. ap Z_inc;am.
am.
rw qMl_comm. am.
ap class_of_in_quotient;ap product_pair_inc.
am. ap Z_inc;am.
ap class_of_in_quotient;ap product_pair_inc.
am. ap Z_inc;am.
Qed.

Lemma qE_reps : forall x, inc x r -> x<>e ->
[J e x] = qE.
Proof.
ir. uf qE.
ap related_classes_eq.
ap product_pair_inc.
am. ap Z_inc;am.
ap product_pair_inc.
am. ap Z_inc;am.
uhg;clear_pr.
rw (ring_0_multl rgH). rw (ring_0_multl rgH).
tv. am. am.
Qed.

Lemma reps_qE : forall a b, inc a r -> inc b r -> b<>e ->
[J a b] = qE -> a=e.
Proof.
ir.
ufi qE H2.
assert (qEquiv (J a b) (J e u)). eapply equivalent_related.
ap qEquiv_equivalence. uhg;ee.
ap product_pair_inc. am. ap Z_inc;am.
ap product_pair_inc. am. ap Z_inc;am.
am.
uh H3;clear_pr_in H3.
rwi (ring_0_multl rgH) H3. apply iH in H3.
nin H3. am. ap False_rect;au.
am. am. am.
Qed.

Lemma qF_simplify : forall x, inc x r -> x<>e -> 
forall a b, inc a r -> inc b r -> b<>e ->
[J (ml x a) (ml x b)] = [J a b].
Proof.
ir.
ap related_classes_eq.
ap product_pair_inc. ap rgH;am.
ap Z_inc. ap rgH;am.
uhg;ir. apply iH in H4. nin H4;au.
am. am.
apply product_pair_inc. am. ap Z_inc;am.
uhg;clear_pr.
assert (associative ml r). am.
wr H4;try am.
symmetry. rw cH;au.
wr H4;try am. rw (cH H1 H2). tv.
ap rgH;am.
Qed.

(* a/b + c/d = (ad + cb)/(bd)*)
Definition qPl0 x y := let a := P x in let b := Q x in let c := P y in let d := Q y in
J (pl (ml a d) (ml c b)) (ml b d).

Lemma qPl0_lci : forall x y, inc x qBase -> inc y qBase -> inc (qPl0 x y) qBase.
Proof.
ir. apply product_pr in H;apply product_pr in H0;ee.
Ztac;clear H2;Ztac;clear H4.
 ap product_pair_inc.
repeat (ap rgH;try am).
ap Z_inc. ap rgH;am.
uhg;ir. apply iH in H4;try am.
nin H4;au. 
Qed.

Lemma qPl0_comm : commutative qPl0 qBase.
Proof.
uhg;ir.
uf qPl0. cp rgH. uh H1;ee.
apply product_pr in H;apply product_pr in H0;ee.
Ztac;clear H6;Ztac;clear H8.
rw H2. rw (cH H9 H6). tv.
ap rgH;am. ap rgH;am.
Qed.

Notation "x + y" := (pl x y).
Notation "x * y" := (ml x y).

Lemma qPl0_compat : forall a b, inc a r -> inc b r -> b<>e -> 
forall a' b', inc a' r -> inc b' r -> b'<>e -> 
qEquiv (J a b) (J a' b') -> 
forall c d, inc c r -> inc d r -> d<>e -> 
forall c' d', inc c' r -> inc d' r -> d'<>e -> 
qEquiv (J c d) (J c' d') -> 
qEquiv (qPl0 (J a b) (J c d)) (qPl0 (J a' b') (J c' d')).
Proof.
ir.
uh H5;clear_pr_in H5;uh H12;clear_pr_in H12.
uhg. uf qPl0. clear_pr.
cp rgH.
cp (integral_quasiregular_right rgH iH).
cp (integral_quasiregular_left rgH iH).
uh H13;ee.
uh H13;ee;uh H17;ee.
rw H23;au.
uh H18;ee.
rw H24;au.
replace (a*d*b') with (a*b'*d).
Focus 2. wr H23;au. wr H23;au. rw (cH H3 H7). tv.
rw H5.
symmetry. rw (cH H0 H7).
rw H23;au. rw H24;au.
replace (c'*b'*d) with (c'*d*b').
Focus 2. wr H23;au;wr H23;au. rw (cH H7 H3). tv.
wr H12.
rw H24;au. rw H24;au.
replace (a' * d' * d * b) with (a' * b * d * d').
replace (c * d' * b' * b) with (c * b * b' * d').
tv.
wr H23;au. wr H23;au. wr H23;au.
rw (cH H3 H0).
assert (inc (b*b') r). ap rgH;am.
wr H23;au. rw (cH H10 H25).
wr H23;au.
wr H23;au. wr H23;au. wr H23;au.
rw (cH H7 H0).
assert (inc (b*d) r). ap rgH;am.
wr H23;au. rw (cH H10 H25).
wr H23;au.
Qed.

Lemma qPl0_compat0 : forall a, inc a qBase -> forall a', inc a' qBase -> qEquiv a a' -> 
forall b, inc b qBase -> forall b', inc b' qBase -> qEquiv b b' -> 
qEquiv (qPl0 a b) (qPl0 a' b').
Proof.
ir.
apply product_pr in H;apply product_pr in H0;apply product_pr in H2;apply product_pr in H3;ee.
apply pair_recov in H;apply pair_recov in H0;apply pair_recov in H2;apply pair_recov in H3.
wr H;wr H0;wr H2;wr H3.
ap qPl0_compat;try am.
eapply Z_sub. am. apply Z_pr in H12;am.
eapply Z_sub. am. apply Z_pr in H10;am.
uhg. clear_pr. am.
eapply Z_sub. am. apply Z_pr in H8;am.
eapply Z_sub. am. apply Z_pr in H6;am.
uhg;clear_pr;am.
Qed.

Definition qPl x y := [qPl0 (rep x) (rep y)].

Lemma qPl_rep_rw0 : forall x y, inc x qBase -> inc y qBase -> 
qPl [x] [y] = [ qPl0 x y ].
Proof.
ir. uf qPl.
ap related_classes_eq. ap qPl0_lci.
cp (class_sub (class_of_class qEquiv H)).
ap H1. eapply class_rep_inc. ap class_of_class. am.
cp (class_sub (class_of_class qEquiv H0)).
ap H1. eapply class_rep_inc. ap class_of_class. am.
ap qPl0_lci;am.
ap qPl0_compat0.
cp (class_sub (class_of_class qEquiv H)).
ap H1. eapply class_rep_inc. ap class_of_class. am.
am.
eapply equivalent_related.
ap qEquiv_equivalence.
uhg. ee.
cp (class_sub (class_of_class qEquiv H)).
ap H1. eapply class_rep_inc. ap class_of_class. am.
am.
ap class_of_rep. ap class_of_in_quotient. am.
cp (class_sub (class_of_class qEquiv H0)).
ap H1. eapply class_rep_inc. ap class_of_class. am.
am.
eapply equivalent_related.
ap qEquiv_equivalence.
uhg. ee.
cp (class_sub (class_of_class qEquiv H0)).
ap H1. eapply class_rep_inc. ap class_of_class. am.
am. ap class_of_rep.
ap class_of_in_quotient. am.
Qed.

Lemma qPl_rep_rw : forall a b, inc a r -> inc b r -> b<>e -> 
forall c d, inc c r -> inc d r -> d<>e -> 
qPl [J a b] [J c d] = [J (pl (ml a d) (ml c b)) (ml b d)].
Proof.
ir. rw qPl_rep_rw0. uf qPl0. clear_pr.
tv. ap product_pair_inc. am. ap Z_inc;am.
ap product_pair_inc. am. ap Z_inc;am.
Qed.

Lemma qPl_lci : is_lci qPl qF.
Proof.
uhg;ir.
uf qPl. ap class_of_in_quotient.
cp (in_quotient_is_class H);cp (in_quotient_is_class H0).
ap qPl0_lci.
assert (sub x qBase).
uh H1;ee. uh H1;ee. am.
ap H3. eapply class_rep_inc. ap H1.
assert (sub y qBase).
uh H2;ee. uh H2;ee. am.
ap H3. eapply class_rep_inc. ap H2.
Qed.

Lemma qPl_comm : commutative qPl qF.
Proof.
uhg;ir.
uf qPl. rw qPl0_comm. tv.
eapply class_sub. ap in_quotient_is_class. ap H.
eapply class_rep_inc. ap in_quotient_is_class. ap H.
eapply class_sub. ap in_quotient_is_class. ap H0.
eapply class_rep_inc. ap in_quotient_is_class. ap H0.
Qed.

Lemma qF_add_group : is_group qPl qF qE.
Proof.
assert (is_neutre qPl qF qE).
uf qE.
uhg. assert (forall x : E, inc x qF -> qPl x [J e u] = x).
ir.
cp (in_quotient_is_class H).
cp (class_of_rep H).
wr H1.
assert (inc (rep x) qBase).
eapply class_sub. ap in_quotient_is_class. ap H.
eapply class_rep_inc. ap in_quotient_is_class. ap H.
apply product_pr in H2;ee. Ztac;clear H4.
rw qPl_rep_rw0. uf qPl0. clear_pr.
rw (ring_0_multl rgH).
cp rgH. uh H4;ee. uh H8;ee.
uh H10;ee. rw H12. rw H12. uh H4;ee.
uh H14;ee. rw H17.
rw (pair_recov H2). tv.
am. am. am. am. ap product_inc. am.
am. ap Z_inc;am. ap product_pair_inc.
ap rgH. ap Z_inc;try ap rgH;am.
ee;au.
ap class_of_in_quotient. ap product_pair_inc.
am. ap Z_inc;am.
ir. rw qPl_comm. ap H;am.
ap class_of_in_quotient. ap product_pair_inc.
am. ap Z_inc;am.
am.

uhg;ee.
ap qPl_lci. am.

uhg;ir.
cp (class_of_rep H0). cp (class_of_rep H1).
cp (class_of_rep H2).
cp (qRep_inc H0). cp (qRep_inc H1). cp (qRep_inc H2).

wr H3. replace (qPl y z) with [qPl0 (rep y) (rep z)].
rw qPl_rep_rw0. rw H3.
replace (qPl x y) with ([qPl0 (rep x) (rep y)]).
wr H5. rw qPl_rep_rw0. rw H5.
uf qPl0. clear_pr.
assert ((P (rep x) * (Q (rep y) * Q (rep z)) +
    (P (rep y) * Q (rep z) + P (rep z) * Q (rep y)) * Q (rep x)) = ((P (rep x) * Q (rep y) + P (rep y) * Q (rep x)) * Q (rep z) +
    P (rep z) * (Q (rep x) * Q (rep y)))).
cp rgH. uh H9;ee.
uh H12;ee. uh H9;ee.
uh H11;ee.
apply product_pr in H6;apply product_pr in H7;apply product_pr in H8;ee.
Ztac;clear H20;Ztac;clear H22;Ztac;clear H24.
rw H13;au. rw H13;au.
rw H15;au.
rw H18;au.
rw (cH H22 H20). rw H18;au.
replace (P (rep y) * Q (rep z) * Q (rep x)) with 
(P (rep y) * (Q (rep z) * Q (rep x)));au.
rw (cH H25 H22). rw H18;au.
replace (Q (rep x) * (Q (rep y) * Q (rep z))) with (Q (rep x) * Q (rep y) * Q (rep z)).
rw H9. tv.
assert (associative ml r). am. symmetry;ap H10.
apply product_pr in H6;ee;Ztac. apply product_pr in H7;ee;Ztac.
apply product_pr in H8;ee;Ztac.
ap qPl0_lci;am. am.
uf qPl. tv. am.
ap qPl0_lci;am.
uf qPl. tv.

ir.
cp (qRep_inc H0).
cp (class_of_rep H0).
apply product_pr in H1;ee. Ztac;clear H4.
assert (is_group pl r e). am.
uh H4;ee. cp (H9 (P (rep x)) H3).
nin H10.
exists [J x0 (Q (rep x))].
uhg. assert (qPl x [J x0 (Q (rep x))] = qE).
wr H2. rw qPl_rep_rw0. rw H2.
uf qPl0.
clear_pr.
cp rgH. uh H11;ee. uh H14;ee.
wr H15. uh H10;ee.
rw H17. rw (ring_0_multl rgH).
ap qE_reps. ap rgH;am.
uhg;ir. apply iH in H19;au. nin H19;au.
am. am. am. am. ap product_inc;try am.
ap Z_inc;am.
ap product_pair_inc. am.
rw H2. ap Z_inc;am.
ee. am.
ap class_of_in_quotient. ap product_pair_inc.
am. ap Z_inc;am.
am. rw qPl_comm. am.
ap class_of_in_quotient. ap product_pair_inc.
am. ap Z_inc;am.
am.
Qed.

Lemma qF_distrib_l : forall a b c, inc a qF -> inc b qF -> inc c qF -> 
qMl a (qPl b c) = qPl (qMl a b) (qMl a c).
Proof.
ir.
cp (class_of_rep H). cp (class_of_rep H0). cp (class_of_rep H1).
cp (qRep_inc H). cp (qRep_inc H0). cp (qRep_inc H1).
apply product_pr in H5;apply product_pr in H6;apply product_pr in H7;ee.
Ztac;clear H9;Ztac;clear H11;Ztac;clear H13.
uf qMl. rw qPl_rep_rw0.
replace ([qMl0 (rep a) (rep (qPl b c))]) with (qMl a (qPl b c)).
uf qPl. wr H2. rw qMl_rep_rw0. rw H2.
uf qMl0;uf qPl0;clear_pr.
set (a0 := P (rep a)). set (a1 := Q (rep a)).
set (b0 := P (rep b)). set (b1 := Q (rep b)).
set (c0 := P (rep c)). set (c1 := Q (rep c)).
ap related_classes_eq.
ap product_pair_inc. repeat (ap rgH;try am).
ap Z_inc. repeat (ap rgH;try am).
uhg;ir. apply iH in H13. nin H13. au.
apply iH in H13. nin H13;au.
am. am. am. ap rgH;am.
ap product_pair_inc. repeat (ap rgH;try am).
ap Z_inc. repeat (ap rgH;try am).
uhg;ir. assert (is_lci ml r). am.
apply iH in H13;au. nin H13;apply iH in H13;au;nin H13;au.
uhg;clear_pr.
assert (forall f:E1, forall x y, x=y -> f x = f y). ir. rw H13. tv.
assert (is_lci pl r). am. assert (is_lci ml r). am.
assert (associative ml r). am.
assert (associative pl r). am.
assert (distributes pl ml r). am.
symmetry.
uh H22;ee.
rw H22;au. rw H23;au.
rw H23;au.
replace (a0 * (b0 * c1) * (a1 * b1 * (a1 * c1))) with 
(a0 * b0 * (a1 * c1) * (a1 * (b1 * c1))).
ap H13. wr H20;au. wr H20;au. symmetry. wr H20;au. ap H13.
wr H20;au. ap H13.
symmetry. wr H20;au. rw cH;au. wr H20;au. ap H13.
wr H20;au. symmetry;wr H20;au. ap H13.
symmetry. wr H20;au.
wr H20;au. wr H20;au. symmetry. wr H20;au.
wr H20;au. ap H13. ap H13.
rw cH;au. wr H20;au. wr H20;au. symmetry.
wr H20;au. ap H13. rw cH;au. wr H20;au.
symmetry. rw cH;au. wr H20;au. wr H20;au. ap H13.
symmetry. wr H20;au. rw cH;au.
symmetry;ap H20;au.

ap product_inc;au. ap Z_inc;am.
ap qPl0_lci;ap product_inc;try am;ap Z_inc;am.
uf qMl. tv.
ap qMl0_lci;ap product_inc;try am;ap Z_inc;am.
ap qMl0_lci;ap product_inc;try am;ap Z_inc;am.
Qed.

Lemma qF_field : is_field qPl qMl qF qE qU.
Proof.
uhg;ee.
uhg;ee.
ap qF_add_group. ap qPl_comm.
ap qF_mult_monoid. uhg;ee.
ir. ap qF_distrib_l;am.
ir. rw qMl_comm;au. rw qF_distrib_l;au.
rw qMl_comm. rw (qMl_comm H1 H0).
tv. am. am. ap qPl_lci;am.

ir. cp (class_of_rep H).
cp (qRep_inc H). apply product_pr in H2;ee.
Ztac;clear H4. apply pair_recov in H2.
wr H1;wr H2.
ap qF_mult_inversible0.
ap product_pair_inc. am. ap Z_inc;am.
uhg;ir.
rwi H2 H4. rwi H1 H4. au.
Qed.

Lemma qPl_same_denom : forall x y q, inc x r -> inc y r -> inc q r -> q<>e ->
qPl [J x q] [J y q] = [J (pl x y) q].
Proof.
ir.
rw qPl_rep_rw;try am.
cp rgH. uh H3;ee. uh H6;ee.
wr H7;try am. rw cH;try am.
rw qF_simplify;try am. tv.
ap rgH;am. ap rgH;am.
Qed.

Lemma qPl_inverse_of_num : forall a b, inc a r -> inc b r -> b<>e -> 
inverse_of qPl qF qE [J a b] = [J (inverse_of pl r e a) b].
Proof.
ir.
eapply inverse_unicity.
ap group_is_monoid. ap qF_field.
ap group_inverse_of. ap qF_field.
ap class_of_in_quotient. ap product_pair_inc.
am. ap Z_inc;am.
uhg. assert (qPl [J a b] [J (inverse_of pl r e a) b] = qE).
rw qPl_same_denom. assert (are_inverse pl r e a (inverse_of pl r e a)).
ap group_inverse_of. am. am.
uh H2;ee. rw H4. ap qE_reps. am. am.
am. ap group_inverse_inc. am. am.
am. am.
assert (A (inc [J a b] qF)
  (inc [J (inverse_of pl r e a) b] qF)).
ee. ap class_of_in_quotient. ap product_pair_inc. am.
ap Z_inc;am. ap class_of_in_quotient. ap product_pair_inc.
ap group_inverse_inc. am. am.
ap Z_inc;am.
ee.
am. am.
am. rw qPl_comm. am.
am. am.
Qed.

Lemma qPl_inverse_of_denom : forall a b, inc a r -> inc b r -> b<>e -> 
inverse_of qPl qF qE [J a b] = [J a (inverse_of pl r e b)].
Proof.
ir.
assert (A (inc [J a b] qF)
  (inc [J a (inverse_of pl r e b)] qF)).
ee.
ap class_of_in_quotient. ap product_pair_inc. am.
ap Z_inc;am.
ap class_of_in_quotient. ap product_pair_inc. am.
ap Z_inc. ap group_inverse_inc. am. am.
uhg;ir. ap H1. assert (are_inverse pl r e b (inverse_of pl r e b)).
ap group_inverse_of;am.
uh H3;ee.
rwi H2 H5. wr H5.
symmetry. ap rgH. am.

eapply inverse_unicity. ap group_is_monoid;ap qF_field.
ap group_inverse_of. ap qF_field.
am. uhg. assert (qPl [J a b] [J a (inverse_of pl r e b)] = qE).
assert (are_inverse pl r e b (inverse_of pl r e b)).
ap group_inverse_of;am.
assert ((inverse_of pl r e b) <> e).
uhg;ir. ap H1. uh H3;ee.
rwi H4 H7. wr H7.
symmetry. ap rgH. am.

rw qPl_rep_rw;try am.
cp rgH. uh H5;ee. uh H9;ee.
wr H9;try am.
uh H3;ee. rw H13.
rw (ring_0_multr rgH);try am.
ap qE_reps. ap rgH;am.
uhg;ir. apply iH in H14;try am. nin H14;au.

ee. am. am. am.
rw qPl_comm. am.
am. am.
Qed.

Lemma qMl_inverse_of : forall a b, inc a r -> inc b r -> a<>e -> b<>e ->
are_inverse qMl qF qU [J a b] [J b a].
Proof.
ir.
assert (inc [J a b] qF).
ap class_of_in_quotient;ap product_pair_inc;try am;ap Z_inc;am.
assert (inc [J b a] qF).
ap class_of_in_quotient;ap product_pair_inc;try am;ap Z_inc;am.
assert (qMl [J a b] [J b a] = qU).
rw qMl_rep_rw;au. uf qU.
rw (cH H H0).
rw qF_simplify;try am.
assert (a = ml a u). symmetry. ap rgH. am.
rw H5. ap qF_simplify. am. am. am. am.
am.

uhg;ee;try am.
rw qMl_comm;am.
Qed.

End Law.

End Fraction_field.
*)


(*interesting note : distributivity does not carry over through innerLaw
sub (A * (B + C)) ((A * B) (A * C)) but not the other way around*)

Module Ordered_ring.
Export Ordered_lci.

Section Law.

Definition order_preserves (le : E2P) (ml : E2) (g : E) (e : E) := 
forall x, inc x g -> le e x -> forall y, inc y g -> le e y -> le e (ml x y).

Definition is_ordered_quasiring pl ml le a e u :=
A (is_quasiring pl ml a e u)
(A (is_order le a)
(A (is_compatible le pl a)
(A (le e u)
(order_preserves le ml a e)))).

Definition is_ordered_ring pl ml le a e u :=
A (is_ring pl ml a e u)
(A (is_order le a)
(A (is_compatible le pl a)
(A (le e u)
(order_preserves le ml a e)))).

Definition is_ordered_field pl ml le a e u := 
A (is_field pl ml a e u)
(A (is_order le a)
(A (is_compatible le pl a)
(A (le e u)
(order_preserves le ml a e)))).

Lemma oring_ml_lcompat : forall le pl ml a e u, is_ordered_ring pl ml le a e u -> 
forall x, inc x a -> le e x -> forall y, inc y a -> forall z, inc z a -> le y z -> 
le (ml x y) (ml x z).
Proof.
ir.
uh H;ee.
assert (le e (pl z (inverse_of pl a e y))).
destruct ordered_group_order_regular with le pl a e.
uhg;ee;am.
apply H10 with y.
am. am. ap H. am. ap group_inverse_inc;am.
assert (associative pl a). am.
assert (is_group pl a e). am.
cp (group_inverse_of H12 H2). uh H13;ee.
wr H11;try am. 
rw H16. uh H12;ee. uh H17;ee.
rw H20;try am;rw H21;try am.
uh H8.
assert (are_inverse pl a e y (inverse_of pl a e y)).
 ap group_inverse_of;am.
uh H10;ee.
assert (le e (ml x (pl z (inverse_of pl a e y)))).
ap H8;try am. ap H;am.
assert (distrib_l pl ml a). am. rwi H15 H14;try am.
wri (inverse_ml_insert_right H) H14;try am.

destruct ordered_group_order_regular with le pl a e.
uhg;ee;am.
assert (are_inverse pl a e (ml x y) (inverse_of pl a e (ml x y))). 
ap group_inverse_of. am.
ap H;am.
eapply H17. ap H18. ap H;am. ap H;am.
uh H18;ee. rw H20. am. 
Qed.


(*
Lemma order_group_opp : forall pl le g e, is_group pl g e -> forall Hc : commutative pl g,
is_order le g -> is_order_compat pl le g -> 
forall x y, inc x g -> inc y g -> le x y -> 
le (inverse_of pl g e y) (inverse_of pl g e x).
Proof.
ir.
cp (group_inverse_of H H2);uh H5;ee. cp (group_inverse_of H H3);uh H9;ee.
uh H;ee.
assert (inverse_of pl g e y = pl x (pl (inverse_of pl g e x) (inverse_of pl g e y))).
rw H14;au. rw H7;au. symmetry;ap H13;au.
assert (inverse_of pl g e x = pl y (pl (inverse_of pl g e y) (inverse_of pl g e x))).
rw H14;au. rw H11;au. symmetry;ap H13;au.

assert (le (pl x (pl (inverse_of pl g e x) (inverse_of pl g e y)))
(pl y (pl (inverse_of pl g e y) (inverse_of pl g e x)))).
rw (Hc (inverse_of pl g e x) (inverse_of pl g e y)).
uh H1;ee.
ap H18. am. am. am. au. au. au.
wri H17 H18;wri H16 H18. am.
Qed.

Lemma order_ring_pos : forall pl ml le a e u, is_ordered_ring pl ml le a e u -> 
forall x y, inc x a -> inc y a -> le x y -> forall z, inc z a -> le e z -> 
le (ml z x) (ml z y).
Proof.
ir.
uh H;ee.
uh H;ee.
uh H11;ee.

assert (le e (pl y (inverse_of pl a e x))).
cp (group_inverse_of H H0). uh H13;ee.
assert (le (pl x (inverse_of pl a e x)) (pl y (inverse_of pl a e x))).
ap H6;au.
rwi H15 H17. am.
uh H8.
cp (H8 z H3 H4).
assert (inc (pl y (inverse_of pl a e x)) a). ap H. am. ap group_inverse_inc. am. am.
cp (H14 (pl y (inverse_of pl a e x)) H15 H13).
clear H14;clear H13;clear H15.
cp (group_inverse_of H H0).
rwi H11 H16;au. Check inverse_ml_insert_right.
assert (is_ring pl ml a e u).
uhg;ee;try am. uhg;ee;am. 
wri (inverse_ml_insert_right H14) H16. clear H14.
assert (le (pl (ml z x) (inverse_of pl a e (ml z x))) (pl (ml z y) (inverse_of pl a e (ml z x)))).
assert (inc (ml z x) a). ap H10;am.
apply (group_inverse_of H) in H14. uh H14;ee.
rw H17. am.
uh H6;ee.
cp (H15 (pl (ml z x) (inverse_of pl a e (ml z x))) (pl (ml z y) (inverse_of pl a e (ml z x)))).
clear H15.
assert (inc (pl (ml z x) (inverse_of pl a e (ml z x))) a).
ap H;au. ap H10;au. ap group_inverse_inc;au.
ap H10;au. cp (H17 H15);clear H17.
assert (inc (pl (ml z y) (inverse_of pl a e (ml z x))) a).
ap H;au. ap H10;au. ap group_inverse_inc;au.
ap H10;au.
cp (H18 H17 H14).
clear H18;clear H17. clear H15.
assert (inc (ml z x) a).
ap H10;am. cp H15.
apply H19 in H15. clear H19.
clear H14.
apply (group_inverse_of H) in H17.
uh H;ee.
uh H17;ee.
cp H14. uh H23;ee.
rwi H21 H15.
rwi H25 H15;au.
wri H18 H15;au.
rwi H22 H15. rwi H24 H15. 
am.
ap H10;au. ap H10;au. am. am.
Qed.

*)

End Law.

End Ordered_ring.


