Set Implicit Arguments.
Unset Strict Implicit.

Require Export functions.

Module Ordinal.
Export Order. Import Map.

Definition is_transitive_set x := forall y, inc y x -> sub y x.

Definition is_ordinal o := 
A (is_transitive_set o)
(A (is_strict_order inc o)
(forall x, sub x o -> nonempty x -> ex (is_min o (leq_of inc) x))).

Lemma ordinal_in_ordinal : forall o, is_ordinal o -> forall x, inc x o -> 
is_ordinal x.
Proof.
ir.
uh H;uhg;ee.

uhg;uhg;ir.
assert (inc y o). apply H with x. am. am.
assert (inc a o). apply H with y;am.
apply H1 with y. am. am. am.
am. am.

uhg;ee. uhg;ir. ap H1. apply H with x. am. am.
uhg;ir. apply H1 with y. apply H with x;am.
apply H with x;am. am. apply H with x;am. am.

ir.
apply H2 in H4.
nin H4. exists x1.
uhg;ee. uhg;ee;ir.
ap H3. am.
ap H4. am. am.
apply sub_trans with x;au.
Qed.

Lemma ordinal_well_order : forall o, is_ordinal o -> is_well_order (leq_of inc) o.
Proof.
ir;uhg;ee. ap order_of_strict. am.
am.
Qed.

Lemma ordinal_not_inc_self : forall o, is_ordinal o -> ~ inc o o.
Proof.
ir;uhg;ir.
eapply H. am. am.
Qed.

Lemma emptyset_ordinal : is_ordinal emptyset.
Proof.
uhg;ee.
uhg;ir.
apply emptyset_empty in H;nin H.

uhg;ee;uhg;ir.
apply emptyset_empty in H;nin H.
apply emptyset_empty in H;nin H.

ir.
nin H0. apply H in H0. apply emptyset_empty in H0;nin H0.
Qed.

Lemma ordinal_segment : forall a b, is_ordinal a -> is_ordinal b -> 
is_initial_segment inc a (inter2 a b).
Proof.
uhg. ir.
ee. uhg;ir;eapply inter2_l;am.
ir.
apply inter2_and in H2;ee.
ap inter2_inc.
uh H;ee. eapply H. am. am.
uh H0;ee. eapply H0. am. am.
Qed.

Lemma ordinal_inc_sub : forall a b, is_ordinal b -> inc a b -> sub a b.
Proof.
intros a b H.
ap H.
Qed.

Lemma transitive_set_union : forall x, (forall y, inc y x -> is_transitive_set y) -> 
is_transitive_set (union x).
Proof.
ir. uhg;ir.
uhg;ir.
ap union_inc.
apply union_ex in H0;nin H0;ee.
cp H0. apply H in H3.
uh H3. cp H2. apply H3 in H4.
cp H1. apply H4 in H5.
exists x0;ee. am. am. 
Qed.

Lemma ordinal_inc_inc_not : forall a b, is_ordinal a -> inc a b -> inc b a -> False.
Proof.
ir.
assert (is_ordinal b).
eapply ordinal_in_ordinal. am. am.
uh H;ee.
eapply H3. am.
uh H2;ee. eapply H2. am. am.
Qed.

Lemma ordinal_inter2_ordinal : forall a b, is_ordinal a -> is_ordinal b -> is_ordinal (inter2 a b).
Proof.
ir. uhg. ee;try uhg;ir.
uhg;ir. ap inter2_inc. uh H;ee;eapply H. eapply inter2_l. am. am.
uh H0;ee;eapply H0. eapply inter2_r. am. am.

ee. uhg;ir.
ap H. apply inter2_l with b;am.
uhg;ir. uh H;ee.
uh H6;ee. eapply H8.
eapply H. eapply inter2_l. ap H2. am.
Focus 2. ap H3. eapply inter2_l. am.
eapply inter2_l. am.
am.

uh H;ee.
apply H4 in H2.
nin H2. exists x0. uhg;ee.
uhg;ee. ap H1. am.
ir. ap H2. am. am.
uhg;ir;eapply inter2_l;au.
Qed.

Lemma ordinal_inc_lt_of : forall a b, is_ordinal a -> is_ordinal b -> (lt_of sub a b) = inc a b.
Proof.
ir;ap iff_eq;ir.
uh H1;ee.
Focus 2.
uhg;ee. ap H0. am.
uhg;ir;subst. eapply H. am. am.

pose (x := complement b a).
assert (nonempty x). ap excluded_middle;uhg;ir.
ap H2. ap extensionality;au;uhg;ir.
ap excluded_middle;uhg;ir. ap H3. econstructor. uf x;ap Z_inc. am. am.
assert (sub x b). uf x. ap Z_sub.
uh H0;ee.
destruct H6 with x as [y H7]. am. am.
assert (inc y x). am. apply Z_all in H8;ee.

assert (y = a).
ap extensionality;uhg;ir.
assert (~ inc a0 x). uhg;ir.
uh H7;ee;uh H7;ee. destruct H13 with a0. am.
apply ordinal_inc_inc_not with y a0. eapply ordinal_in_ordinal. Focus 2. ap H8.
uhg;ee;am. am. am. subst.
eapply ordinal_not_inc_self. eapply ordinal_in_ordinal. uhg;ee;am. am. am.
eapply use_complement. Focus 2. am.
eapply H0. ap H8. am.

assert (inc a0 b). au.

destruct well_order_total with (leq_of inc) b y a0;au.
uhg;ee. ap order_of_strict. am. am.
nin H12. 
ap False_rect. ap H9.
uh H;ee. eapply H. am. am.
subst. ap False_rect.
au.
nin H12;subst;au.
ap False_rect. au.
subst. am.
Qed.

Lemma ordinal_sub_leq_of : forall a b, is_ordinal a -> is_ordinal b -> sub a b = leq_of inc a b.
Proof.
ir.
ap iff_eq;ir. uhg.
apply by_cases with (a=b);ir;au.
wr ordinal_inc_lt_of. uf lt_of. left;ee;am.
am. am.
nin H1. ap H0. am.
subst;ap sub_refl.
Qed.

Lemma ordinal_inc_eq_inc : forall a b, is_ordinal a -> is_ordinal b -> 
(inc a b \/ (a=b \/ inc b a)).
Proof.
ir.
pose (d := inter2 a b).
assert (sub d a). uhg;ir;eapply inter2_l;am.
assert (sub d b). uhg;ir;eapply inter2_r;am.

assert (is_ordinal d). uf d. ap ordinal_inter2_ordinal;am.
rwi ordinal_sub_leq_of H1;au.
rwi ordinal_sub_leq_of H2;au.
nin H1;nin H2;subst.
ap False_rect. apply ordinal_not_inc_self with d;au. ap inter2_inc. am. am.
right;right. wr H2. am.
left;wr H1;am.
right;left. wr H1. am.
Qed.

Lemma ordinal_inc_S_all : forall o, is_ordinal o -> inc emptyset (oS o).
Proof.
ir. uf oS;rw tack_on_inc. destruct (ordinal_inc_eq_inc emptyset_ordinal H);au.
nin H0;subst;au.
edestruct emptyset_empty;am.
Qed.

Lemma ordinal_inc_neq : forall o, is_ordinal o -> forall x, inc x o -> x<>o.
Proof.
uhg;ir. subst.
eapply ordinal_not_inc_self;am.
Qed.

Lemma ordinal_sub_sub : forall a b, is_ordinal a -> is_ordinal b -> 
(sub a b \/ sub b a).
Proof.
ir.
cp (ordinal_inc_eq_inc H H0). nin H1.
left. ap H0;am.
nin H1;subst. left;ap sub_refl.
right;ap H;am.
Qed.

Lemma ordinal_sub_total_order : forall o, is_ordinal o -> is_total_order sub o.
Proof.
ir. uhg;ee. uhg;ee. uhg;ir;ap sub_refl.
uhg;ir;ap extensionality;am.
uhg;ir;apply sub_trans with y;am.
uhg;ir. ap ordinal_sub_sub;apply ordinal_in_ordinal with o;am.
Qed.

Lemma ordinal_inc_wf : forall x, (forall y, inc y x -> is_ordinal y) -> nonempty x -> 
ex (is_min x (leq_of inc) x).
Proof.
ir.
nin H0.
apply by_cases with (inter2 x0 x = emptyset);ir.
exists x0;uhg;ee. uhg;ee.
am. ir. cp (H x0 H0). cp (H x1 H2).
destruct (ordinal_inc_eq_inc H3 H4).
uhg. au. nin H5;subst;au.
uhg;au. uhg. ap False_rect.
eapply emptyset_empty.
wr H1. ap inter2_inc. am. am.
am.

assert (nonempty (inter2 x0 x)).
ap excluded_middle;uhg;ir;ap H1. ap empty_emptyset.
ir. ap H2;econstructor;am.
assert (is_ordinal x0). au.
uh H3;ee. destruct H5 with (inter2 x0 x).
uhg;ir;eapply inter2_l;am. am.
exists x1;uhg;ee. uhg;ee.
eapply inter2_r;am. ir.

uhg;apply by_cases with (x1=x2);ir;au.
left.
destruct ordinal_inc_eq_inc with x0 x2.
au. au.
assert (is_ordinal x2). au.
uh H10;ee. eapply H10.
am. am.
nin H9;subst.
am.
uh H6;ee;uh H6;ee. destruct H11 with x2.
ap inter2_inc;am. am. subst. ap False_rect;au.
eapply inter2_r;am.
Qed.

Lemma ordinal_inc_trans : forall a b c, inc a b -> inc b c -> is_ordinal c -> inc a c.
Proof.
ir.
assert (is_ordinal b).
apply ordinal_in_ordinal with c;am.
assert (is_ordinal a).
apply ordinal_in_ordinal with b;am.

wr ordinal_inc_lt_of;au.
uhg;ee.
wri ordinal_inc_lt_of H;au;wri ordinal_inc_lt_of H0;au.
uh H;uh H0;ee.
apply sub_trans with b;au.
uhg;ir;subst.
apply ordinal_inc_inc_not with b c;au.
Qed.

Lemma transitive_union_ordinal : forall x, is_transitive_set x -> 
(forall o, inc o x -> is_ordinal o) -> is_ordinal (union x).
Proof.
ir. uhg;ee.
uhg;ir. uhg;ir.
ap union_inc. apply union_ex in H1;nin H1;ee.
econstructor. ee.  am. destruct H0 with x0. am.
ee. eapply H4. am. am.
uhg;ee. uhg;ir.
apply union_ex in H1;nin H1;ee.
destruct H0 with x1;au;ee.
ap H4. am.
uhg;ir. apply union_ex in H1;apply union_ex in H2;apply union_ex in H4.
nin H1;nin H2;nin H4;ee.
assert (is_ordinal x1 & is_ordinal x2 & is_ordinal x3). ee;au. ee.
cp (ordinal_sub_sub H9 H10).
cp (ordinal_sub_sub H9 H11).
cp (ordinal_sub_sub H11 H10).
destruct H12.
destruct H14.
apply H10 with y;au. apply H11 with y;au.
destruct H13. apply H11 with y;au. apply H9 with y;au.

ir.
destruct ordinal_inc_wf with x0.
ir. cp (H1 y H3).
apply union_ex in H4;nin H4;ee.
apply ordinal_in_ordinal with x1;au.
am.
exists x1. uhg;ee.
uhg;ee. ap H1;am.
ir. ap H3. am.
am.
Qed.

Lemma ordinal_S : forall o, is_ordinal o -> is_ordinal (oS o).
Proof.
ir. uf oS.
uhg;ee.
uhg;ir. ufi oS H0. rwi tack_on_inc H0. nin H0.
uf oS. uhg;ir;rw tack_on_inc. left. uh H;ee;eapply H. am. am.
subst. uhg;ir;uf oS;rw tack_on_inc. au.

uhg;ee;uhg;ir. rwi tack_on_inc H0;nin H0;subst.
ap H;am. ap ordinal_not_inc_self;am.
rwi tack_on_inc H0;rwi tack_on_inc H1;rwi tack_on_inc H3.
nin H0;nin H1;nin H3;subst.
apply H with y;am.
am. ap False_rect.
apply ordinal_not_inc_self with o. am.
apply ordinal_inc_trans with z. am. am. am. am.
ap False_rect.
apply ordinal_not_inc_self with o. am.
apply ordinal_inc_trans with y. am. am. am.

apply ordinal_inc_trans with y. am. am. am.
am. am.

ir.
uh H;ee.
apply by_cases with (nonempty (inter2 o x));ir.
apply H3 in H4.
nin H4. exists x0;uhg;ee. uhg;ee.
rw tack_on_inc. left;am.
ir.
cp (H0 x1 H5). rwi tack_on_inc H6;nin H6;subst.
ap H4. ap inter2_inc;am.
uhg. left. am.
eapply inter2_r;am.
ap inter2_l.

assert (x = singleton o).
ap extensionality;uhg;ir.
apply by_cases with (a=o);ir.
subst. ap singleton_inc.
destruct H4. exists a. ap inter2_inc.
apply H0 in H5. rwi tack_on_inc H5;nin H5. am.
destruct H6;am.
am.
apply singleton_eq in H5;subst.
ap excluded_middle;uhg;ir.
nin H1. ap H4. exists x0. ap inter2_inc;au.
cp H1. apply H0 in H1. rwi tack_on_inc H1. nin H1.
am. subst. destruct H5;am.
subst.
exists o. uhg;ee.
uhg;ee. rw tack_on_inc;au.
ir. uhg;right. symmetry;ap singleton_eq;am.
ap singleton_inc.
Qed.

Lemma ordinal_oS_inj : forall a, is_ordinal a -> forall b, oS a = oS b -> a=b.
Proof.
assert (forall a, is_ordinal a -> forall b, is_ordinal b -> oS a = oS b -> sub a b).
ir.
destruct ordinal_inc_eq_inc with a b;try am.
rw ordinal_sub_leq_of;au. left;am.
nin H2. subst. ap sub_refl.
assert (inc a (oS b)). wr H1;rw oS_inc;au.
rwi oS_inc H3;nin H3.
ap False_rect;eapply ordinal_inc_inc_not. Focus 2. am.
am. am.
subst. ap sub_refl.

ir.
assert (is_ordinal b).
apply ordinal_in_ordinal with (oS a).
ap ordinal_S;am.
rw H1;rw oS_inc;au.
ap extensionality;ap H;au.
Qed.

Lemma nNum_ordinal : forall n, inc n nNum -> is_ordinal n.
Proof.
ap nNum_rect.
ap emptyset_ordinal.
ir. ap ordinal_S;am.
Qed.

Notation ω := nNum.

Lemma omega_transitiveT : is_transitive_set nNum.
Proof.
uhg. ap nNum_rect.
ap emptyset_sub_all.
ir.
uhg;ir. ufi oS H1;rwi tack_on_inc H1;nin H1.
ap H0;am. subst. am.
Qed.

Lemma omega_union : nNum = union nNum.
Proof.
ap extensionality;uhg;ir.
Focus 2. apply union_ex in H;nin H;ee. eapply omega_transitiveT.
am. am.

ap union_inc. econstructor. ee.
eapply oS_nNum. am.
uf oS;rw tack_on_inc;au.
Qed.

Lemma omega_ordinal : is_ordinal nNum.
Proof.
rw omega_union.
ap transitive_union_ordinal. ap omega_transitiveT.
ap nNum_ordinal.
Qed.

Lemma ordinal_ind : forall (p : EP), (forall o, is_ordinal o -> (forall a, inc a o -> p a) -> p o) -> 
forall o, is_ordinal o -> p o.
Proof.
ir. ap excluded_middle;uhg;ir.
pose (z := Z o (fun x =>  ~ p x)).
destruct ordinal_inc_wf with z. ir.
apply Z_all in H2. ee. apply ordinal_in_ordinal with o;am.
ap excluded_middle;uhg;ir;ap H1;ap H;try am.
ir. ap excluded_middle;uhg;ir. ap H2;exists a;ap Z_inc;am.
uh H2;ee. apply Z_all in H3.
ee.
ap H4. ap H. apply ordinal_in_ordinal with o;am.
ir. ap excluded_middle;uhg;ir.
uh H2;ee. destruct H7 with a. ap Z_inc.
uh H0;ee. eapply H0. am. am.
am.
eapply ordinal_inc_inc_not. apply ordinal_in_ordinal with o;am. am. am.
subst. apply ordinal_not_inc_self with a. apply ordinal_in_ordinal with o;am.
am.
Qed.

Lemma nNum_wo_ind : forall (p : EP), (forall n, inc n nNum -> (forall a, inc a n -> p a) -> p n) ->
forall n, inc n nNum -> p n.
Proof.
intros p IH.
pose (p' := fun o => inc o nNum -> p o).
assert (forall n, is_ordinal n -> p' n).
ap ordinal_ind;uf p';ir.
ap IH. am. ir. ap H0. am. eapply omega_transitiveT. am. am.
ir. ap H. ap nNum_ordinal;am. am.
Qed.

Definition successor_ordinal x := exists o, is_ordinal o & x = oS o.

Lemma successor_is_ordinal : forall x, successor_ordinal x -> is_ordinal x.
Proof.
ir;nin H;ee;subst;ap ordinal_S;am.
Qed.

Definition limit_ordinal x := A (is_ordinal x) (A (nonempty x) (~ successor_ordinal x)).

Lemma limit_is_ordinal : forall x, limit_ordinal x -> is_ordinal x.
Proof.
ir;am.
Qed.

Definition finite_ordinal x := A (is_ordinal x) (forall y, is_ordinal y -> sub y x -> (y=emptyset \/ successor_ordinal y)).

Lemma finite_ordinal_in_finite_ordinal : forall x, finite_ordinal x -> 
forall y, inc y x -> finite_ordinal y.
Proof.
uhg;ir;ee. apply ordinal_in_ordinal with x;am.
ir. ap H. am. wri ordinal_inc_lt_of H0.
eapply sub_trans;am. apply ordinal_in_ordinal with x;am.
am.
Qed.

Lemma finite_S : forall o, finite_ordinal o -> finite_ordinal (oS o).
Proof.
ir. uhg;ee. ap ordinal_S. am.
ir. rwi ordinal_sub_leq_of H1. nin H1. ufi oS H1. rwi tack_on_inc H1.
nin H1. ap H. am. rw ordinal_sub_leq_of. left;am. am. am.
subst. ap H. am. ap sub_refl. subst. right. exists o;ee. am. tv.
am. ap ordinal_S;am. 
Qed.

Lemma nNum_finite_ordinals : forall n, inc n nNum -> finite_ordinal n.
Proof.
ap nNum_rect.
uhg;ee. ap emptyset_ordinal.
ir. left. ap extensionality;au;ap emptyset_sub_all.

intros n H. ap finite_S.
Qed.

Lemma finite_ordinal_nNum : forall o, finite_ordinal o -> inc o nNum.
Proof.
ir. ap excluded_middle;uhg;ir.
pose (y := complement (oS o) nNum).
assert (nonempty y). exists o. ap Z_inc. uf oS;rw tack_on_inc;au.
am.

assert (is_ordinal (oS o)). ap ordinal_S;am.
uh H2;ee. clear H3;clear H2. apply H4 in H1.
nin H1. clear H4.
assert (finite_ordinal x).
apply finite_ordinal_in_finite_ordinal with (oS o).
ap finite_S. am. am.
uh H2. ee. destruct H3 with x.
am. ap sub_refl.
subst. uh H1;ee. apply Z_all in H4. ee.
ap H5. ap emptyset_N.
nin H4. ee. subst.
uh H1;ee. apply Z_all in H5. ee.
ap H6. ap oS_nNum.
ap excluded_middle;uhg;ir.
assert (inc x0 y). ap Z_inc. assert (is_ordinal (oS o)).
ap ordinal_S. am. uh H8;ee;eapply H8.
am. uf oS;rw tack_on_inc;au.
am.
apply H1 in H8.
wri ordinal_sub_leq_of H8. apply ordinal_not_inc_self with x0.
am. ap H8. uf oS;rw tack_on_inc;au.
ap ordinal_S;am. am.
ap Z_sub.
Qed.

Lemma class_initial_is_ordinal : forall x, (forall y, inc y x -> is_ordinal y) -> 
(forall b, inc b x -> forall c, inc c b -> inc c x) -> 
is_ordinal x.
Proof.
ir;uhg;ee. uhg. uhg;ir;eapply H0;am.
uhg;ee. uhg;ir.
ap ordinal_not_inc_self. ap H;am.
uhg. ir. eapply ordinal_inc_trans. am. am. ap H.
am.

ir. destruct ordinal_inc_wf with x0.
ir;ap H;au.
am.
exists x1. erewrite <-sub_min. am. am.
ap sub_refl.
Qed.

Lemma omega_least_limit : forall o, limit_ordinal o -> sub nNum o.
Proof.
ir. destruct ordinal_inc_eq_inc with o nNum.
am. ap omega_ordinal.
apply nNum_finite_ordinals in H0. uh H;ee.
nin H2. uh H0;ee. destruct H2 with o.
am. ap sub_refl. subst. nin H1. apply emptyset_empty in H1;nin H1.
am.
nin H0. subst. ap sub_refl. ap H. am.
Qed.

Lemma omega_is_limit : limit_ordinal nNum.
Proof.
uhg;ee. ap omega_ordinal.
exists emptyset. ap emptyset_N.
uhg;ir. nin H.
ee.
assert(inc x nNum). rw H0. uf oS;rw tack_on_inc;au.
assert (inc (oS x) nNum). ap oS_nNum. am.
wri H0 H2. destruct ordinal_not_inc_self with nNum.
ap omega_ordinal. am.
Qed.

Lemma ordinal_ind_cases : forall (p : EP), p emptyset -> 
(forall o, is_ordinal o -> p o -> p (oS o)) -> 
(forall o, limit_ordinal o -> (forall x, inc x o -> p x) -> p o) -> 
forall o, is_ordinal o -> p o.
Proof.
intros p H H0 H1. ap ordinal_ind.
ir. apply by_cases with (successor_ordinal o). ir.
nin H4. ee. subst.
ap H0. am. ap H3. uf oS. rw tack_on_inc;au.
ir. apply by_cases with (o=emptyset);ir.
subst. am.
ap H1. uhg. ee. am. ap excluded_middle;uhg;ir;ap H5;ap extensionality;uhg;ir.
nin H6;exists a;am. apply emptyset_empty in H7;nin H7.
am. am.
Qed.

Lemma ordinal_sub_ind : forall (p : E2P) (a : E), is_ordinal a -> 
p a a -> 
(forall b, is_ordinal b -> sub a b -> p a b -> p a (oS b)) -> 
(forall b, limit_ordinal b -> inc a b -> (forall x, inc x b -> sub a x -> p a x) -> p a b) -> 
forall b, is_ordinal b -> sub a b -> p a b.
Proof.
intros p a Hoa Hpaa HS HL.
pose (p' := fun b => sub a b -> p a b).
assert (forall b, is_ordinal b -> p' b).
 ap ordinal_ind_cases;try am;uf p';ir.
assert (a = emptyset). ap emptyset_sub_is.
am.
subst. am.
rwi ordinal_sub_leq_of H1. nin H1.
assert (sub a o). rwi oS_inc H1;nin H1. ap H. am.
subst;ap sub_refl. ap HS. am. am. ap H0. am.
subst. am.
am. ap ordinal_S;am.
rwi ordinal_sub_leq_of H1;try am. nin H1.
ap HL. am. am. am. subst. am.
am.
Qed.

Lemma ordinal_inc_sub_trans : forall a, 
forall b, is_ordinal b -> inc a b -> 
forall c, is_ordinal c -> sub b c -> 
inc a c.
Proof.
ir.
assert (is_ordinal a). apply ordinal_in_ordinal with b;am.
rwi ordinal_sub_leq_of H2;au.
nin H2. apply ordinal_inc_trans with b;am. subst.
am.
Qed.

Lemma ordinal_sub_inc_trans : forall a, is_ordinal a -> 
forall b, sub a b -> 
forall c, is_ordinal c -> inc b c -> 
inc a c.
Proof.
ir. assert (is_ordinal b).
apply ordinal_in_ordinal with c;am.
rwi ordinal_sub_leq_of H0;au. nin H0.
apply ordinal_inc_trans with b;am.
subst;am.
Qed.

Import Function.

Definition approx g d h := A (is_ordinal d) 
(A (Function.axioms h)
(A (domain h = d)
(forall x, inc x d -> ev h x = g (restr h x)))).

Lemma approx_restr : forall g, forall d h, approx g d h -> forall o, inc o d -> approx g o (restr h o).
Proof.
ir. uh H;ee;uhg;ee. apply ordinal_in_ordinal with d;am.
ap restr_axioms. am. rw restr_domain. ap extensionality;uhg;ir.
eapply inter2_r;am. ap inter2_inc. rw H2. uh H;ee;eapply H. am. am.
am.
am. ir.
rw restr_ev. rw H3.
ap uneq. ap extensionality;uhg;ir.
apply Z_all in H5. ee.
ap Z_inc. ap Z_inc. am. assert (is_ordinal o). apply ordinal_in_ordinal with d;am.
uh H7;ee;eapply H7. am. am. am.
apply Z_all in H5;ee;apply Z_all in H5;ee;ap Z_inc. am.
am. uh H;ee;eapply H. am. am. am. am.
rw H2. uh H;ee;eapply H;am.
Qed.

Lemma approx_unicity : forall g d, unicity (approx g d).
Proof.
intros g. pose (fun d => forall h h' : E, approx g d h -> approx g d h' -> h = h').
assert (forall d, is_ordinal d -> P d).
cp (approx_restr (g:=g)).
ap ordinal_ind;uf P;ir.
uh H2;ee;uh H3;ee.
ap function_extensionality;eauto.
rw H8;am. rw H5;ir.
rw H6;try am;rw H9;try am.
ap uneq. apply H1 with x. am.
apply approx_restr with o. uhg;ee;am. am.
apply approx_restr with o. uhg;ee;am. am.
uhg;ufi P H;ir;eapply H;am.
Qed.

Lemma approx_sub : forall g, forall d d', sub d d' -> 
forall h h', approx g d h -> approx g d' h' -> sub h h'.
Proof.
intros g.
ir.
rwi ordinal_sub_leq_of H. nin H.
assert (h = restr h' d).
eapply approx_unicity. am.
eapply approx_restr. am. am.
subst. ap Z_sub.
subst. assert (h = h').
eapply approx_unicity. am.
am. rw H;ap sub_refl.
am. am.
Qed.

Lemma approx_ex : forall g d, is_ordinal d -> ex (approx g d).
Proof.
intros g. ap ordinal_ind_cases;ir.
exists emptyset. uhg;ee.
ap emptyset_ordinal. 
uhg. ee. uhg. ir. emptyset_auto.
uhg;uhg;ir. emptyset_auto.
ap empty_emptyset;ir.
ufi domain H. apply Z_pr in H. nin H.
eapply emptyset_empty;au.
ir;ap False_rect;eapply emptyset_empty;au.

nin H0.
pose (h := tack_on x (J o (g x))).
ufi tack_on h.
assert (axioms x). am. assert (domain x = o). am.
set (h0 := singleton (J o (g x))) in *.
assert (axioms h0). uf h0. ap singleton_axioms.
assert (domain h0 = singleton o). ap singleton_domain.
assert (inter2 (domain x) (domain h0) = emptyset). ap empty_emptyset;ir.
apply inter2_and in H5;ee. rwi H4 H6. apply singleton_eq in H6.
rwi H6 H5;rwi H2 H5;eapply H. am. am.
assert (axioms h). uf h.
ap union2_axioms;am.
assert (domain h = (oS o)). uf h. rw union2_domain;try am.
rw H2;rw H4. uf oS. reflexivity.
exists h. uhg;ee;try am.
ap ordinal_S;am.
ir. ufi oS H8;rwi tack_on_inc H8;nin H8.
assert (restr h x0 = restr x x0).
ap extensionality;uhg;ir;apply Z_all in H9;ee.
ap Z_inc. ufi h H9. apply union2_or in H9;nin H9.
am. apply singleton_eq in H9. rwi H9 H10;clpri H10.
ap False_rect;eapply ordinal_inc_inc_not. am. am. am. am.
ap Z_inc;try am. uf h. ap union2_l. am.
rw H9. transitivity (ev x x0).
uf h. ap union2_ev_l;try am. rw H2;am.
ap H0. am. rw H8.
assert (restr h o = x). uf h;ap extensionality;uhg;ir.
apply Z_all in H9;ee. apply union2_or in H9;nin H9.
am. apply singleton_eq in H9. rwi H9 H10. clpri H10.
edestruct ordinal_not_inc_self. am. am.
ap Z_inc. ap union2_l;am. wr H2.
ap domain_P_in. am. am.
rw H9.
uf h. rw union2_ev_r. uf h0.
symmetry. ap fun_show_ev;au. ap singleton_inc. am. am.
am. uf h0;rw singleton_domain;ap singleton_inc.

assert (o = union o).
ap extensionality;uhg;ir.
ap union_inc. ap excluded_middle;uhg;ir.
assert (forall y, inc y o -> sub y a).
ir. assert (is_ordinal y). apply ordinal_in_ordinal with o;am.
assert (is_ordinal a). apply ordinal_in_ordinal with o;am.
nin (ordinal_sub_sub H4 H5). am. rwi ordinal_sub_leq_of H6.
nin H6. nin H2. exists y;ee;am.
subst. ap sub_refl.
am. am.
ap H. uhg. exists a.
ee. apply ordinal_in_ordinal with o;am.
assert (is_ordinal a). apply ordinal_in_ordinal with o;am.
ap extensionality;uhg;ir.
uf oS;rw tack_on_inc.
cp H5. apply H3 in H6. rwi ordinal_sub_leq_of H6.
au. apply ordinal_in_ordinal with o;am.
am. ufi oS H5;rwi tack_on_inc H5. nin H5.
uh H;ee. uh H;ee. eapply H. am. am.
subst. am.
apply union_ex in H1;nin H1;ee.
uh H;ee;uh H;ee;eapply H;am.
pose (z := (Im (fun x => unique_choose (approx g x)) o)).
assert (forall y, inc y z -> exists x, inc x o & approx g x y).
ir.
apply Im_ex in H2;nin H2;ee. exists x;ee. am. rw H3. ap unique_choose_pr.
 ap H0;am. uhg;ir;eapply approx_unicity;am.
assert (forall x y, inc x o -> approx g x y -> inc y z).
ir. uf z. ap Im_show_inc. exists x;ee. am.
eapply approx_unicity. am. ap unique_choose_pr;au. ap approx_unicity.
assert (forall f, inc f z -> axioms f). ir. apply H2 in H4;nin H4;ee;am.
assert (union_cond z). uhg.
ir. apply H2 in H5;apply H2 in H6.
nin H5;nin H6;ee.
assert (domain f = x0). am. assert (domain g0 = x1). am.
rwi H11 H7. rwi H12 H8.
assert (is_ordinal x0 & is_ordinal x1). ee;am.
ee.
nin (ordinal_sub_sub H13 H14).
eapply sub_ev_eq. am. eapply approx_sub. am.
am. am. rw H11;am.
symmetry.
eapply sub_ev_eq. am. eapply approx_sub. am.
am. am. rw H12;am.

pose (h := union z).
assert (axioms h). ap union_compatible_axioms;am.
assert (domain h = o). uf h. rw union_compatible_domain.
rw H1. ap uneq.
ap extensionality;uhg;ir. apply Im_ex in H7;nin H7. ee.
rw H8;clear H8;clear a. apply H2 in H7.
nin H7;ee. uh H8;ee. rw H10.
am.
ap Im_show_inc. cp H7.
apply H0 in H8. nin H8.
cp H8. apply H3 in H9.
exists x;ee. am. symmetry;am.
am.
am. am.
exists h;uhg;ee. am. am. am.
ir.

assert (inc (oS x) o).
assert (is_ordinal (oS x)). ap ordinal_S;apply ordinal_in_ordinal with o;am.
destruct ordinal_inc_eq_inc with o (oS x). am. am.
ufi oS H10. rwi tack_on_inc H10. nin H10.
destruct ordinal_inc_inc_not with o x;am.
destruct ordinal_not_inc_self with o. am. wri H10 H8. am.
nin H10. uh H;ee. nin H12.
exists x. ee. apply ordinal_in_ordinal with o;am.
am.
am.
cp H9. apply H0 in H10;nin H10;cp H10. apply H3 in H11.
Focus 2. am.
transitivity (ev x0 x). uf h. eapply union_compatible_ev.
am. am. am. uh H10;ee. rw H13.
uf oS;rw tack_on_inc;au.
uh H10;ee.
rw H14. ap uneq.

ap extensionality;uhg;ir; apply Z_all in H15;ee.
assert (approx g (oS x) x0). uhg;ee;am.
ap Z_inc. uf h. ap union_inc. exists x0. ee. am. am.
am.
ufi h H15;apply union_ex in H15;nin H15;ee.
cp H15. apply H2 in H18.
nin H18;ee.
assert (approx g (oS x) x0). uhg;ee;am.
assert (approx g x (restr x0 x)). eapply approx_restr. am.
uf oS;rw tack_on_inc;au.
assert (is_ordinal x). am. assert (is_ordinal x2). apply ordinal_in_ordinal with o;am.
destruct (ordinal_sub_sub) with x x2;try am.
assert (sub (restr x0 x) x1). eapply approx_sub. am. am. am.
assert (inc (P a) (domain (restr x0 x))).
rw restr_domain;try am. ap inter2_inc.
rw H13. uf oS;rw tack_on_inc;au. am.
apply domain_ev_inc in H26;try am.
cp H26. apply H25 in H27.
assert (a = J (P a) (ev (restr x0 x) (P a))).
assert (is_pair a). eapply H19. am.
nin H28. clpr;clpri H27. ap uneq.
eapply H19. Focus 2. am.
ap H17.
rw H28. ap domain_ev_inc. ap restr_axioms.
am. rw restr_domain;try am. ap inter2_inc. rw H13.
uf oS;rw tack_on_inc;au. am.
assert (sub x1 (restr x0 x)). eapply approx_sub.
am. am. am.
ap H25. am.
uf oS. rw tack_on_inc. au.
Qed.

Lemma ordinal_rec_ex : forall g : E1, exists f : E1, forall o, is_ordinal o -> 
f o = g (Function.create o f).
Proof.
ir.
set (f0 := (fun o => unique_choose (approx g (oS o)))).
assert (forall o, is_ordinal o -> approx g (oS o) (f0 o)).
ir;uf f0. ap unique_choose_pr. ap approx_ex. ap ordinal_S;am.
ap approx_unicity.
assert (forall a b, is_ordinal a -> is_ordinal b -> sub a b -> sub (f0 a) (f0 b)).
ir. assert (sub (oS a) (oS b)).
uhg;ir. ufi oS H3;rwi tack_on_inc H3. nin H3;
uf oS;rw tack_on_inc.
au. subst. rwi ordinal_sub_leq_of H2;au.
eapply approx_sub. am. ap H;am. ap H;am.

assert (forall o, is_ordinal o -> approx g o (L o (fun a => ev (f0 a) a))).
ap ordinal_ind.
ir.
uhg;ee. am. ap create_axioms. ap create_domain.
ir. rw create_ev.
assert (is_ordinal x). apply ordinal_in_ordinal with o;am.
apply H in H4.
uh H4;ee. rw H7.
ap uneq. ap extensionality;uhg;ir;apply Z_all in H8;ee.
ap Z_inc. uf L. ap Im_show_inc.
cp H8. apply H5 in H10.
nin H10.
clpri H9.
exists a;ee. uh H1;ee;eapply H1. am. am.
ap uneq. eapply H5. am.
assert (is_ordinal x). apply ordinal_in_ordinal with o;am.
assert (is_ordinal a). apply ordinal_in_ordinal with x;am.
assert (sub a x). rw ordinal_sub_leq_of;au. uhg;au.
apply H0 in H12;try am.
ap H12.
cp H11;apply H in H13.
 ap domain_ev_inc. am. uh H13;ee. rw H15.
uf oS;rw tack_on_inc;au.
am.
cp H8.
apply Im_ex in H10. nin H10;ee;subst.
clpri H9.
assert (is_ordinal x0). apply ordinal_in_ordinal with o;am.
assert (is_ordinal x). apply ordinal_in_ordinal with o;am.
assert (sub x0 x). rw ordinal_sub_leq_of;au. uhg;au.
cp H12;apply H in H14.
cp H11;apply H in H15.
assert (sub (oS x0) (oS x)).
uf oS;uhg;ir. rwi tack_on_inc H16;rw tack_on_inc.
nin H16. left;au. subst.
rwi ordinal_sub_leq_of H13;au.
assert (sub (f0 x0) (f0 x)). eapply approx_sub;try am.
assert (ev (f0 x0) x0  = ev (f0 x) x0).
eapply sub_ev_eq. am. am. uh H15;ee. rw H19. uf oS;rw tack_on_inc;au.
rw H18.
assert (ev (f0 x) x0 = ev (restr (f0 x) x) x0).
symmetry. ap restr_ev. am. am.
uh H14;ee.  rw H20. ap H16. uf oS;rw tack_on_inc;au.
rw H19. ap domain_ev_inc.
ap restr_axioms. am.
rw restr_domain;au. ap inter2_inc.
uh H14;ee. rw H21. ap H16;uf oS;rw tack_on_inc;au.
am. uf oS;rw tack_on_inc;au. am. 

exists (fun o => ev (f0 o) o).
ir.
cp H2; apply H in H3. uh H3;ee.
rw H6. ap uneq.
eapply approx_unicity.
Focus 2. ap H1. am.
uhg;ee. am. ap restr_axioms;am.
rw restr_domain. rw H5. uf oS. ap extensionality;uhg;ir.
apply inter2_and in H7;am.
ap inter2_inc. rw tack_on_inc;au. am.
am.
ir. rw restr_ev. rw H6.
ap uneq. ap extensionality;uhg;ir.
apply Z_all in H8;ee. ap Z_inc. ap Z_inc. am.
uh H2;ee;eapply H2. am. am. am.
apply Z_all in H8;ee;apply Z_all in H8;ee.
ap Z_inc;am.
uf oS;rw tack_on_inc;au. am. am.
rw H5. uf oS;rw tack_on_inc;au.
uf oS;rw tack_on_inc;au.
Qed.

Definition ordinal_rec : E1 -> E1.
intros g o.
ap ev. ap unique_choose.
ap approx. ap g.
ap oS. ap o.  ap o.
Defined.

Lemma approx_unique_choose : forall g o, is_ordinal o -> 
approx g o (unique_choose (approx g o)).
Proof.
ir;ap unique_choose_pr.
ap approx_ex. am.
ap approx_unicity.
Qed.

Lemma ordinal_rec_pr : forall g, forall o, is_ordinal o -> ordinal_rec g o = 
g (Function.create o (ordinal_rec g)).
Proof.
intro g. ap ordinal_ind;ir.
assert (forall a, inc a o -> approx g a (L a (ordinal_rec g))).
ir. uhg;ee. eapply ordinal_in_ordinal;am.
ap create_axioms. ap create_domain.
ir. rw create_ev;au. rw H0;au.
ap uneq. assert (sub x a). rw ordinal_sub_leq_of.
uhg;au. apply ordinal_in_ordinal with a.
apply ordinal_in_ordinal with o;am.
am.
apply ordinal_in_ordinal with o;am.
ap function_extensionality;ir.
ap create_axioms. ap restr_axioms. ap create_axioms.
rw create_domain. rw restr_sub_domain. tv.
ap create_axioms. rw create_domain. am.
rwi create_domain H4. rw create_ev;au. rw restr_ev;au. rw create_ev;au.
ap create_axioms. rw create_domain. au.
uh H;ee;eapply H. am. am.

cp (approx_unique_choose g (ordinal_S H)).
uh H2. ee.
etransitivity. uf ordinal_rec. reflexivity.
rw H5.
ap uneq. eapply approx_unicity.
eapply approx_restr. uhg;ee;am.
rw oS_inc;au.
uhg;ee. am. ap create_axioms. ap create_domain.
ir. rw create_ev;au.
rw H0;au. ap uneq.

etransitivity.
symmetry. ap restr_eq. ap create_axioms.
Focus 2. rw create_domain.
rw create_domain. ap H. am.
ap create_axioms.
ir. rwi create_domain H7. rw create_ev;au. rw create_ev;au.
uh H;ee;eapply H;am.
rw create_domain. tv.
rw oS_inc;au. 
Qed.

Lemma rec_pr_approx : forall g f, (forall o, is_ordinal o -> f o = g (Function.create o f)) -> 
forall o, is_ordinal o -> approx g o (Function.create o f).
Proof.
ir. uhg;ee.
am. ap create_axioms. ap create_domain.
ir. assert (is_ordinal x). apply ordinal_in_ordinal with o;am.
rw create_ev;au.
rw H;au. ap uneq.
ap function_extensionality. ap create_axioms.
ap restr_axioms;ap create_axioms.
rw create_domain. rw restr_domain. rw create_domain.
assert (sub x o). rw ordinal_sub_leq_of;au. uhg;eau.
ap extensionality;uhg;ir;try ap inter2_inc;au.
eapply inter2_r;am.
ap create_axioms. ir.
rwi create_domain H3.
rw create_ev. rw restr_ev. rw create_ev.
tv. uh H0;ee; eapply H0;am. ap create_axioms.
am. rw create_domain. uh H0;ee;eapply H0;am.
am.
Qed.

Lemma ordinal_rec_approx : forall g o, is_ordinal o -> approx g o (L o (ordinal_rec g)).
Proof.
intros g. ap rec_pr_approx.
ir.
ap ordinal_rec_pr. am.
Qed.

Definition ordinal_rec_cases (v0 : E) (fS : E2) (fH : E1) := 
ordinal_rec (fun ha => if eq_dec (domain ha) emptyset then v0
else let a := domain ha in by_cases
(fun _ : successor_ordinal a => fS (union a) (ev ha (union a)))
(fun _ : ~successor_ordinal a => fH ha)).

Lemma ordinal_rec_case_0 : forall v0 fS fH, ordinal_rec_cases v0 fS fH emptyset = v0.
Proof.
ir;uf ordinal_rec_cases. rw ordinal_rec_pr.
rw create_domain. rw eq_dec_if. tv. ap emptyset_ordinal.
Qed.

Lemma rec_pr_unicity : forall g f f', (forall o, is_ordinal o -> f o = g (Function.create o f)) -> 
(forall o, is_ordinal o -> f' o = g (Function.create o f')) -> 
forall o, is_ordinal o -> f o = f' o.
Proof.
ir.
cp (rec_pr_approx H). cp (rec_pr_approx H0).
assert (L (oS o) f = L (oS o) f'). eapply approx_unicity.
ap H2. ap ordinal_S;am.
ap H3;ap ordinal_S;am.
apply (uneq (fun f => ev f o)) in H4.
rwi create_ev H4. rwi create_ev H4. am. 
uf oS;rw tack_on_inc;au. uf oS;rw tack_on_inc;au.
Qed.

Lemma ordinal_limit_union_self : forall o, limit_ordinal o -> union o = o.
Proof.
ir. uh H;ee.
ap extensionality;uhg;ir.
apply union_ex in H2;nin H2;ee.
uh H;ee;eapply H;am.

ap union_inc;ap excluded_middle;uhg;ir.
ap H1. exists a. ee. apply ordinal_in_ordinal with o;am.
assert (is_ordinal a). apply ordinal_in_ordinal with o;am.
assert (is_ordinal (oS a)). ap ordinal_S;am.
destruct ordinal_inc_eq_inc with o (oS a);try am.
ufi oS H6;rwi tack_on_inc H6;nin H6.
destruct ordinal_inc_inc_not with o a;try am.
subst. uh H;ee. ap False_rect. eapply H6;try am.
nin H6. am.
nin H3. exists (oS a). ee. am. uf oS;rw tack_on_inc;au.
Qed.

Lemma ordinal_union_S : forall o, is_ordinal o -> union (oS o) = o.
Proof.
ir. ap extensionality;uhg;ir.
apply union_ex in H0;nin H0;ee.
ufi oS H0;rwi tack_on_inc H0;nin H0.
uh H;ee;eapply H;am.
subst. am.
ap union_inc. exists o;ee.
uf oS;rw tack_on_inc;au.
am.
Qed.

Lemma ordinal_rec_case_S : forall v0 fS fH o, is_ordinal o -> 
ordinal_rec_cases v0 fS fH (oS o) = fS o (ordinal_rec_cases v0 fS fH o).
Proof.
ir.
uf ordinal_rec_cases. rw ordinal_rec_pr.
rw create_domain. rw eq_dec_if_not. rw by_cases_if.
rw ordinal_union_S;au. rw create_ev;au.
rw oS_inc;au. exists o. ee;au.
uhg;ir;apply emptyset_empty with o. wr H0;rw oS_inc;au.
ap ordinal_S;am.
Qed.

Lemma ordinal_rec_case_limit : forall v0 fS fH o, limit_ordinal o -> 
ordinal_rec_cases v0 fS fH o = fH (L o (ordinal_rec_cases v0 fS fH)).
Proof.
ir;uf ordinal_rec_cases;rw ordinal_rec_pr;au.
rw create_domain. rw eq_dec_if_not. rw by_cases_if_not.
tv. am. uhg;ir.
subst. uh H;ee. nin H0. eapply emptyset_empty;am.
Qed.


Lemma ordinal_S_inc_inc : forall a b, is_ordinal a -> is_ordinal b -> inc a b -> 
inc (oS a) (oS b).
Proof.
ir.
cp ordinal_S.
wr ordinal_inc_lt_of;au.
uhg;ee. uhg;ir.
ufi oS H3. rwi tack_on_inc H3. nin H3.
uf oS;rw tack_on_inc;au. left.
uh H0;ee. eapply H0. am. am.
subst. uf oS;rw tack_on_inc;au.
uhg;ir. cp (uneq (union) H3).
rwi ordinal_union_S H4. rwi ordinal_union_S H4.
subst. eapply H. am. am. am. am.
Qed.

Lemma ordinal_limit_gt : forall o, limit_ordinal o -> forall x, inc x o -> 
inc (oS x) o.
Proof.
ir. assert (is_ordinal x). apply ordinal_in_ordinal with o;am.
cp ordinal_S.
destruct ordinal_inc_eq_inc with (oS x) o;au.
nin H3. subst. ap False_rect. ap H. exists x. ee. am. tv.
ufi oS H3;rwi tack_on_inc H3;nin H3.
destruct ordinal_inc_inc_not with o x;au.
subst. destruct ordinal_not_inc_self with x;au.
Qed.

Lemma union_sub_upper : forall x, 
forall y, inc y x -> sub y (union x).
Proof.
ir;uhg;ir;ap union_inc. exists y;ee. am. am.
Qed.

Definition well_founded_on (r:E2P) (p:EP) := forall q : EP, (exists x, p x & q x) -> 
exists x, p x & q x & (forall y, p y -> q y -> r x y).

Lemma ordinal_wf : well_founded_on sub Ordinal.is_ordinal.
Proof.
uhg;ir.
nin H;ee.
uh H;ee.
pose (z := Z x q).
apply by_cases with (nonempty z);ir.
apply H2 in H3.
nin H3. exists x0. ee.
apply ordinal_in_ordinal with x. uhg;ee;am. am.
eapply Z_pr;am. ir.
destruct ordinal_sub_sub with x y.
uhg;ee;am.
am.
apply sub_trans with x.
ap H. am.
am.

rwi ordinal_sub_leq_of H6.
nin H6.
rw ordinal_sub_leq_of. ap H3.
ap Z_inc. am. am. apply ordinal_in_ordinal with x. uhg;ee;am. am.
am. subst.
ap H. am.
am. uhg;ee;am.
ap Z_sub.

exists x;ee.
uhg;ee;am. am.
ir.
destruct ordinal_inc_eq_inc with x y. uhg;ee;am. am.
ap H4. am.
nin H6. rw H6. ap sub_refl.
destruct H3. exists y. ap Z_inc. am. am.
Qed.


Lemma ordinal_union : forall x, (forall y, inc y x -> is_ordinal y) -> 
is_ordinal (union x).
Proof.
ir.
uhg;ee;try uhg;ee;try uhg;ir.
apply union_ex in H0;nin H0;ee;ap union_inc.

exists x0;ee. am. assert (is_ordinal x0). au.
uh H3;ee. eapply H3;am.
ap ordinal_not_inc_self;au.
apply union_ex in H0;nin H0;ee. apply ordinal_in_ordinal with x1;au.
apply union_ex in H0;apply union_ex in H1;apply union_ex in H3.
nin H0;nin H1;nin H3;ee.
assert (is_ordinal x1 & is_ordinal x2 & is_ordinal x3);ee;au.
apply ordinal_inc_trans with y. am. am.
apply ordinal_in_ordinal with x3;am.

destruct ordinal_wf with (fun a => inc a x0).
nin H1. exists x1;ee;au.
apply H0 in H1. apply union_ex in H1;nin H1;ee.
apply ordinal_in_ordinal with x2;au.
ee.

assert (forall a, inc a (union x) -> is_ordinal a).
ir. apply union_ex in H5;nin H5;ee. apply ordinal_in_ordinal with x2;au.
exists x1. uhg;ee. uhg;ee.
ap H0. am.

ir. assert (is_ordinal x1). au.
assert (is_ordinal x2). au.
wr ordinal_sub_leq_of;au.
am.
Qed.

Lemma ordinal_sub_not_inc : forall a b, is_ordinal a -> is_ordinal b -> sub a b = ~ inc b a.
Proof.
ir;ap iff_eq;ir.
uhg;ir. eapply H0. ap H1. am. ap H1;am.
destruct (ordinal_inc_eq_inc H H0).
rw ordinal_sub_leq_of;au. uhg;au.
rw ordinal_sub_leq_of;au. uhg;au. nin H2. au.
nin H1;am.
Qed.

Lemma ordinal_inc_not_sub : forall a b, is_ordinal a -> is_ordinal b -> inc a b = ~ sub b a.
Proof.
ir. rw ordinal_sub_not_inc;au. ap iff_eq;ir. uhg;ir;au. ap excluded_middle;am.
Qed.


Lemma ordinal_union_sup : forall x, (forall y, inc y x -> is_ordinal y) -> 
forall y, is_ordinal y -> (forall a, inc a x -> sub a y) -> sub (union x) y.
Proof.
ir. assert (is_ordinal (union x)). 
ap ordinal_union.
am.
rw ordinal_sub_not_inc;au. uhg;ir. cp H3.
apply union_ex in H3;nin H3;ee.
cp H3. apply H1 in H6.
assert (is_ordinal x0). au.
rwi ordinal_sub_not_inc H6. au. am. am.
Qed.

Lemma ordinal_union_sub : forall x, (forall y, inc y x -> is_ordinal y) -> 
forall x', (forall y, inc y x' -> is_ordinal y) -> 
(forall y, inc y x -> exists y', inc y' x' & sub y y') -> 
sub (union x) (union x').
Proof.
ir.
ap ordinal_union_sup.
am.
ap ordinal_union. am.
ir. cp H2. apply H1 in H3. nin H3;ee.
uhg;ir. ap union_inc.
exists x0;ee;au.
Qed.

Lemma ordinal_not_set : ~ exists x, forall o, is_ordinal o -> inc o x.
Proof.
uhg;ir;nin H.
pose (z := Z x is_ordinal).
assert (forall o, is_ordinal o -> inc o z). ir;ap Z_inc;au.
assert (forall o, inc o z -> is_ordinal o);ir. eapply Z_pr;am.
assert (is_ordinal (union z)).
ap ordinal_union. am.
assert (z = union z). ap extensionality;uhg;ir.
ap union_inc. exists (oS a). ee. ap H0;ap ordinal_S;au.
uf oS;rw tack_on_inc;au.
apply union_ex in H3;nin H3;ee. ap H0.
apply ordinal_in_ordinal with x0;au.
wri H3 H2. eapply H2.
ap H0. am. ap H0. am.
Qed.

Lemma ordinal_sub_wo : forall o, is_ordinal o -> is_well_order sub o.
Proof.
ir. uhg;ee. uhg;ee;uhg;ir.
ap sub_refl. ap extensionality;am. apply sub_trans with y;am.
uh H;ee. ir. apply H1 in H3;au.
nin H3. exists x. uhg;ee. uhg;ee. am. ir. rw ordinal_sub_leq_of. ap H3. am.
apply ordinal_in_ordinal with o;try am. uhg;ee;am.
apply ordinal_in_ordinal with o;try am. uhg;ee;am.
au.
am.
Qed.

Lemma ordinal_sub_total : forall o, is_ordinal o -> is_total_order sub o.
Proof.
ir. uhg;ee. ap ordinal_sub_wo;am. apply well_order_total. ap ordinal_sub_wo.
am.
Qed.


Lemma ordinal_isomorphism_rw : forall a b, is_ordinal a -> is_ordinal b -> 
forall f, is_isomorphism inc a inc b f = is_isomorphism sub a sub b f.
Proof.
ir;ap iff_eq;ir.
uhg;ee. uhg;ee. am.
ir. rw ordinal_sub_leq_of. rwi ordinal_sub_leq_of H4.
nin H4;uhg. left. ap H1. am. am. am.
right;rw H4;tv.
apply ordinal_in_ordinal with a;am. apply ordinal_in_ordinal with a;am.
apply ordinal_in_ordinal with b;try am;eapply trans_of_map;am. 
apply ordinal_in_ordinal with b;try am;eapply trans_of_map;am.
am. 

uhg;ee. uhg;ee. am.
ir. wr ordinal_inc_lt_of. wri ordinal_inc_lt_of H4.
nin H4;uhg. ee. ap H1. am. am. am.
uhg;ir. ap H5;ap H1. am. am. am.
apply ordinal_in_ordinal with a;am. apply ordinal_in_ordinal with a;am.
apply ordinal_in_ordinal with b;try am;eapply trans_of_map;am. 
apply ordinal_in_ordinal with b;try am;eapply trans_of_map;am.
am. 
Qed.

Lemma ordinal_only_isomorphism : forall a, is_ordinal a -> 
forall b, is_ordinal b -> forall f, is_isomorphism inc a inc b f -> f = id a.
Proof.
ir.
assert (forall x, inc x a -> A (ev f x = Z b (fun y => inc y (ev f x))) (ev f x = Im (ev f) x)). ir.
dj.
ap extensionality;uhg;ir. ap Z_inc.
uh H0;ee;eapply H0. eapply trans_of_map. am. am. am. am.
apply Z_pr in H3. am.

ap extensionality;uhg;ir.
cp H4. rwi H3 H5. apply Z_sub in H5.
apply H1 in H5. nin H5;ee.
subst. ap Im_inc.
wr ordinal_inc_lt_of. eapply total_injective_lt_back.
assert (is_total_order sub a).
uhg;ee. uhg;ee. uhg. ir. ap sub_refl. uhg. intros x1 xH y xH0. ap extensionality.
uhg. ir;eapply sub_trans;am.
uhg. ir. ap ordinal_sub_sub. apply ordinal_in_ordinal with a;am.
apply ordinal_in_ordinal with a;am.
am. Focus 2. rwi ordinal_isomorphism_rw H1. am.
am. am.
uhg;ee. uhg. ir. ap sub_refl. uhg. intros x1 xH y xH0. ap extensionality.
uhg. ir;eapply sub_trans;am.
am. am. am. rw ordinal_inc_lt_of. am.
apply ordinal_in_ordinal with b;try am;eapply trans_of_map;am.
apply ordinal_in_ordinal with b;try am;eapply trans_of_map;am.
apply ordinal_in_ordinal with a;am. apply ordinal_in_ordinal with a;am.
apply Im_ex in H4;nin H4;ee;subst.
ap H1. uh H;ee. eapply H.
am. am. am. am.

assert (forall x, inc x a -> ev f x = x).
pose (p :=  fun x => inc x a -> ev f x = x).
assert (forall x, is_ordinal x -> p x). ap ordinal_ind;uf p;ir.
cp H5. apply H2 in H6.
ee. rw H7.
ap extensionality_rw;ir. rw Im_rw.
ap iff_eq;ir. nin H8;ee;subst.
rw H4. am. am. uh H;ee;eapply H. am. am.
exists a0;ee. am.
symmetry. ap H4. am. uh H;ee;eapply H;am.
ir;ap H3;try am. apply ordinal_in_ordinal with a;am.

assert (domain f = a). uh H1;ee. uh H1;ee;ap H1.
ap function_extensionality.
am. ap id_axioms. rw id_domain. am.
rw H4;ir. rw id_ev. ap H3. am. am.
Qed.

Lemma ordinal_isomorphic_unicity : forall a b, is_ordinal a -> is_ordinal b -> 
are_rel_isomorphic sub a sub b -> a=b.
Proof.
ir. nin H1.
cp H1. wri ordinal_isomorphism_rw H2. apply ordinal_only_isomorphism in H2.
subst.
uh H1;ee. apply bijective_range in H2. rwi id_range H2. am.
am. am. am. am.
Qed.


Lemma ordinal_nonempty_emptyset_inc : forall o, is_ordinal o -> 
nonempty o -> inc emptyset o.
Proof.
ir. destruct ordinal_inc_eq_inc with emptyset o;au.
ap emptyset_ordinal.
nin H1. subst.
nin H0. edestruct emptyset_empty. am.
edestruct emptyset_empty. am.
Qed.

Lemma finite_ordinal_not_sub_limit : forall o, limit_ordinal o -> 
forall n, inc n nNum -> ~iso_sub o n.
Proof.
intros o Ho.
ap nNum_rect;uhg;ir.
nin H. ee.
assert (x = emptyset). ap extensionality.
am. ap emptyset_sub_all. subst;clear H0.
uh Ho. ee.
nin H1. nin H. apply (bijective_of_map H) in H1.
edestruct emptyset_empty. ap H1.

nin H1. ee.
assert (inc n x).
ap excluded_middle;uhg;ir.
ap H0. uhg. exists x;ee.
am.
uhg;ir. cp H4. apply H2 in H4.
ufi oS H4;rwi tack_on_inc H4;nin H4;au.
subst. nin H3;am.
assert (are_equipotent (oS o) o).
assert (Application.bijective o (oS o) (fun x => if eq_dec x emptyset then o else
if P_dec (inc x nNum) then union x else x)).
uhg;ee. uhg;ir.
nin (eq_dec x0 emptyset). subst. uf oS;rw tack_on_inc;au.
nin (P_dec (inc x0 nNum)).
apply nNum_destruct in a. nin a.
nin b;am.
nin H5;ee;subst.
rw ordinal_union_S. 
uf oS;rw tack_on_inc. left.
uh Ho;ee. uh H6;ee;eapply H6. 
ap H4. uf oS;rw tack_on_inc;au.
ap nNum_ordinal. am.
uf oS;rw tack_on_inc;au.

uhg;ir.
nin (eq_dec x0 emptyset) ; nin (eq_dec y emptyset).
subst. tv.
nin (P_dec (inc y nNum)).
subst. union_nin H5.
destruct ordinal_inc_inc_not with y x0.
ap nNum_ordinal;am. am. am.
subst. edestruct ordinal_not_inc_self. am. am.
subst. nin (P_dec (inc x0 nNum)).
union_nin H4. destruct ordinal_inc_inc_not with x0 x1;au.
ap nNum_ordinal;am.
edestruct ordinal_not_inc_self;am.
nin (P_dec (inc x0 nNum));nin (P_dec (inc y nNum));subst.
apply nNum_destruct in a;apply nNum_destruct in a0;nin a;nin a0;subst.
nin b;tv. nin b;tv.
nin b0;tv.
nin H7;nin H8;ee;subst.
cp (nNum_ordinal).
rwi ordinal_union_S H6;au.
rwi ordinal_union_S H6;au.
ap uneq;am.
nin b1.
apply nNum_destruct in a;nin a;subst.
nin b;tv. nin H6;ee;subst.
cp nNum_ordinal.
rw ordinal_union_S;au.
nin b1.
apply nNum_destruct in a;nin a;subst.
nin b0;tv. nin H6;ee;subst.
cp nNum_ordinal.
rw ordinal_union_S;au.
tv.

uhg;ir.
ufi oS H4;rwi tack_on_inc H4;nin H4.
nin (P_dec (inc y nNum)).
exists (oS y). ee.
ap ordinal_limit_gt. am. am. (*this is where we need o to be a limit ordinal*)
rw eq_dec_if_not. rw P_dec_if.
ap ordinal_union_S. ap nNum_ordinal;am.
ap ordinal_limit_gt. ap omega_is_limit.
am. uhg;ir.
destruct emptyset_empty with y. wr H5.
uf oS;rw tack_on_inc;au.
exists y;ee.
am. rw eq_dec_if_not. rw P_dec_if_not.
tv. am. uhg;ir;subst;ap b. ap emptyset_N.
subst. exists emptyset;ee.
ap ordinal_nonempty_emptyset_inc. am.
am.
rw eq_dec_if. tv.
ap are_equipotent_sym. econstructor.
ap map_of_bijective. am.
assert (are_equipotent (oS o) x).
apply are_equipotent_trans with o. am.
am.
pose (y := Z x (fun z => z<>n)).
assert (sub y n).
uhg;ir. apply Z_all in H6. nin H6.
cp H6. apply H2 in H8. ufi oS H8;rwi tack_on_inc H8;nin H8.
am. subst. nin H7;tv.
ap H0. exists y. ee. Focus 2. am.

assert (x = tack_on y n). ap extensionality;uhg;ir.
rw tack_on_inc;au. apply by_cases with (a=n);ir.
au. left. ap Z_inc. am. am.
rwi tack_on_inc H7;nin H7;subst;au. eapply Z_sub;am.

assert (are_equipotent (oS o) (tack_on y n)).
wr H7. am.
ufi oS H8. wri tack_on_equipotent H8.
am. ap ordinal_not_inc_self;am.
uhg;ir. apply Z_pr in H9. au.
Qed.

Lemma finite_ordinal_equipotent_eq : forall a, finite_ordinal a -> forall b, is_ordinal b -> are_equipotent a b -> 
a=b.
Proof.
pose ( p:= fun a => forall b, is_ordinal b -> are_equipotent a b -> a=b).
assert (forall a, inc a nNum -> p a).
ap nNum_rect;uf p;ir.
symmetry. nin H0. ap empty_emptyset;ir.
apply H0 in H1. nin H1;ee. eapply emptyset_empty;am.
assert (nonempty b).
nin H2.
assert (inc n (oS n)).
uf oS;rw tack_on_inc;au.
uh H2;ee. apply trans_of_map in H2. apply H2 in H3.
exists (ev x n);am.
apply by_cases with (successor_ordinal b);ir.
nin H4. ee;subst.
ap uneq. ap H0. am.

assert (exists f, Application.bijective (oS n) (oS x) f).
nin H2. econstructor. ap bijective_of_map. am.
nin H5.
assert (inc x (oS x)).
uf oS;rw tack_on_inc;au. apply H5 in H6. nin H6;ee.
ufi oS H6;rwi tack_on_inc H6;nin H6.

pose (f := fun a => if eq_dec a x1 then x0 n else x0 a).
assert (Application.bijective n x f).
uhg;ee;uhg;ir.
uf f. nin (eq_dec x2 x1).
assert (inc (x0 n) (oS x)).
ap H5. uf oS;rw tack_on_inc;au.
ufi oS H9;rwi tack_on_inc H9;nin H9.
am. wri H7 H9.
apply H5 in H9;au.
subst.
ap False_rect. assert (is_ordinal x1).
apply ordinal_in_ordinal with nNum. ap omega_ordinal.
am. eapply H7;am.
uf oS;rw tack_on_inc;au.
uf oS;rw tack_on_inc;au.
assert (inc x2 (oS n)).
uf oS;rw tack_on_inc;au. apply H5 in H9.
ufi oS H9;rwi tack_on_inc H9;nin H9.
am. wri H7 H9.
nin b. ap H5;au;uf oS;rw tack_on_inc;au.

ufi f H10.
assert (is_ordinal n).
apply ordinal_in_ordinal with nNum.
 ap omega_ordinal.
am.
nin (eq_dec x2 x1);nin (eq_dec y x1).
rw a;au.
apply H5 in H10.
ap False_rect.
wri H10 H9. eapply H11;am.
uf oS;rw tack_on_inc;au. uf oS;rw tack_on_inc;au.
apply H5 in H10.
ap False_rect.
rwi H10 H8. eapply H11. ap H8. am.
uf oS;rw tack_on_inc;au. uf oS;rw tack_on_inc;au.
ap H5;au.
uf oS;rw tack_on_inc;au. uf oS;rw tack_on_inc;au.

assert (inc y (oS x)).
uf oS;rw tack_on_inc;au.
apply H5 in H9. nin H9;ee.
wr H10.
uf f. ufi oS H9;rwi tack_on_inc H9;nin H9.
exists x2. ee. am.
rw eq_dec_if_not. tv.
uhg;ir. rwi H11 H10.
rwi H7 H10.
wri H10 H8.
eapply H4;am.
exists x1;ee. am.
rw eq_dec_if. rw H9. tv.
econstructor. ap map_of_bijective.
am.
subst.
set (x := x0 n) in *.
assert (Application.bijective n x x0).
assert (forall a, sub a (oS a)). uhg. uf oS;ir;rw tack_on_inc;au.
assert (forall a, inc a (oS a)). uf oS;ir;rw tack_on_inc;au.
uhg;ee;uhg;ir.
cp H8. apply H6 in H9.
apply H5 in H9.
ufi oS H9;rwi tack_on_inc H9;nin H9.
am.
ufi x H9. apply H5 in H9;au.
subst.
ap False_rect.
assert (is_ordinal n).
apply ordinal_in_ordinal with nNum.
 ap omega_ordinal.
am.
eapply H9;am.
ap H6. am.
ap H5;au. ap H6;au. ap H6;am.
cp H8. apply H6 in H9.
apply H5 in H9. nin H9;ee.
ufi oS H9;rwi tack_on_inc H9;nin H9.
exists x1;ee;au.
ufi x H8. subst.
assert (inc (x0 n) (oS x)).
ap H5. au.
ap False_rect. eapply H1. am. am.
econstructor. ap map_of_bijective. am.

assert (limit_ordinal b). uhg;ee;am.
edestruct finite_ordinal_not_sub_limit.
am. Focus 2. exists (oS n). ee. ap are_equipotent_sym;am.
ap sub_refl. ap oS_nNum. am.

ufi p H. ir. ap H.
ap finite_ordinal_nNum. am. am. am.
Qed.

Lemma nNum_ordinal_equipotent_eq : forall n, inc n nNum -> forall m, is_ordinal m -> are_equipotent n m -> 
n=m.
Proof.
intros n H. ap finite_ordinal_equipotent_eq. ap nNum_finite_ordinals.
am.
Qed.

Lemma nNum_equipotent_eq : forall n, inc n nNum -> forall m, inc m nNum -> 
are_equipotent n m -> n=m.
Proof.
intros n H m H0. ap nNum_ordinal_equipotent_eq. am. ap nNum_ordinal;am.
Qed.

Lemma iso_sub_equipotent_tack_on : forall a, iso_sub nNum a -> 
forall x, are_equipotent a (tack_on a x).
Proof.
ir.
apply by_cases with (inc x a);ir.
assert (a = tack_on a x). ap extensionality_rw;ir;rw tack_on_inc;ap iff_eq;ir.
au. nin H1;subst;au.
wr H1. ap are_equipotent_refl.

nin H. ee.
nin H.
cp (bijective_of_map H).
cp emptyset_N. apply H2 in H3.
assert (forall y, inc y x0 -> y<>ev x1 emptyset -> exists n, inc n nNum & y = ev x1 (oS n)).
ir. apply H2 in H4. nin H4;ee.
subst. apply nNum_destruct in H4. nin H4.
subst. nin H5;tv.
nin H4;ee;subst. exists x3;ee;au.

assert (forall n m, inc n nNum -> inc m nNum -> ev x1 (oS n) = ev x1 (oS m) -> n=m).
ir. ap oS_N_inj. am. ap H2. ap oS_nNum. am. ap oS_nNum. am.
am.

assert (Application.bijective a (tack_on a x) (fun z => 
if eq_dec z (ev x1 emptyset) then x else
if P_dec (inc z x0) then ev x1 (unique_choose (fun t => inc t nNum & z = ev x1 (oS t)))
else z)).
assert (forall z, z<>ev x1 emptyset -> inc z x0 -> 
 (fun t : E => t ∈ ω & z = ev x1 (oS t)) (unique_choose (fun t : E => t ∈ ω & z = ev x1 (oS t)))).
ir. ap unique_choose_pr. ap H4. am. am.
uhg;ir. ee. ap H5;au. etransitivity. symmetry;am. am.
simpl in H6.

uhg;ee;uhg;ir.
nin (eq_dec x2 (ev x1 emptyset)).
rw tack_on_inc. au.
nin (P_dec (inc x2 x0)).
destruct H6 with x2. am. am.
rw tack_on_inc. left.
ap H1. ap H2. am.
rw tack_on_inc;au.

nin (eq_dec x2 (ev x1 emptyset));nin (eq_dec y (ev x1 emptyset)).
rw a0. au.
nin (P_dec (inc y x0)).
nin H0.
rw H9. ap H1. ap H2.
ap H6. am. am.
nin H0. rw H9. am.
nin (P_dec (inc x2 x0)).
nin H0. wr H9. ap H1;ap H2;ap H6.
am. am.
nin H0. wr H9. am.
nin (P_dec (inc x2 x0));nin (P_dec (inc y x0)).
destruct H6 with x2;try am. destruct H6 with y;try am.
rw H11;rw H13. ap uneq;ap uneq.
ap H2. am. am. am.

nin b1. wr H9. destruct H6 with x2;try am.
ap H2. am.
nin b1. rw H9. ap H2. ap H6. am. am.
am.

rwi tack_on_inc H7;nin H7.
nin (eq_dec y (ev x1 emptyset)).
subst. exists (ev x1 (oS emptyset)).
ee. ap H1. ap H2. ap oS_nNum;ap emptyset_N.
rw eq_dec_if_not. rw P_dec_if.
destruct H6 with (ev x1 (oS emptyset)).
uhg;ir. apply H2 in H8. destruct emptyset_empty with emptyset. wr H8.
uf oS;rw tack_on_inc. au.
ap oS_nNum;ap emptyset_N.
ap emptyset_N.
ap H2. ap oS_nNum;ap emptyset_N.
apply H5 in H9.
wr H9. tv.
ap emptyset_N. am.
ap H2;ap oS_nNum;ap emptyset_N.
uhg;ir. apply H2 in H8. destruct emptyset_empty with emptyset. wr H8.
uf oS;rw tack_on_inc. au.
ap oS_nNum;ap emptyset_N.
ap emptyset_N.

apply by_cases with (inc y x0);ir.
destruct H4 with y;au.
ee.
subst.
assert (inc (oS (oS x2)) nNum).
repeat ap oS_nNum. am.
assert (ev x1 (oS (oS x2)) <> ev x1 emptyset).
uhg;ir. apply H2 in H11;au.
destruct emptyset_empty with (oS x2).
wr H11. uf oS;rw tack_on_inc;au.
ap emptyset_N.

exists (ev x1 (oS (oS x2))). ee.
ap H1. ap H2;am.
rw eq_dec_if_not. rw P_dec_if.
destruct H6 with (ev x1 (oS (oS x2))).
am. ap H2;am.
ap uneq. apply H2 in H13;au.
ap oS_N_inj. am. 
wr H13.  tv.
ap oS_nNum;am.
ap H2;am.
am.

exists y;ee. am. rw eq_dec_if_not. rw P_dec_if_not.
tv. am. am.
subst. exists (ev x1 emptyset). ee.
ap H1. ap H2. ap emptyset_N.
rw eq_dec_if. tv.

econstructor;ap map_of_bijective;am.
Qed.

Definition o1 := oS emptyset.
Definition o2 := oS (oS emptyset).

Lemma o1_rw : o1 = singleton emptyset.
Proof.
uf o1. uf oS. ap extensionality_rw;ir;rw tack_on_inc;ap iff_eq;ir.
nin H. edestruct emptyset_empty;am.
subst;ap singleton_inc.
right. ap singleton_eq. am.
Qed.

Lemma o1_N : inc o1 nNum.
Proof.
ap oS_nNum. ap emptyset_N.
Qed.

Lemma o2_rw : o2 = doubleton emptyset (o1).
Proof.
uf o2. fold o1. ap extensionality_rw;ir.
rw oS_inc. rw doubleton_pr. uf o1. rw oS_inc.
ap iff_eq;ir;repeat nin H;au.
edestruct emptyset_empty;am.
Qed.

End Ordinal.

Module Sow. 
Export Ordinal.


Definition is_sow (p:EP) o :=
is_ordinal o & ((exists x, is_ordinal x & p x) -> 
p o & (forall y, is_ordinal y -> p y -> sub o y)) & 
((forall x, is_ordinal x -> ~ p x) -> o=emptyset).

Definition sow (p:EP) :=
unique_choose (is_sow p). 

Lemma sow_exists : forall p, exists o, is_sow p o.
Proof.
ir. 
apply by_cases with (exists x, is_ordinal x & p x).
ir. 
apply ordinal_wf in H. nin H;ee. exists x;uhg;ee;au.
ir. ap False_rect. apply H2 with x;am.
exists emptyset;uhg;ee. ap emptyset_ordinal.
ir. destruct H;am.
ir;destruct H;econstructor;ee;am.
ir;tv.
Qed. 

Lemma sow_is_sow : forall p, is_sow p (sow p). 
ir. cp (sow_exists p). 
apply unique_choose_pr in H.
Proof.
am.
uhg;ir.
apply by_cases with (exists x, is_ordinal x & p x);ir.
nin H0;nin H1. ee.
clear H7;clear H5.
cp (H3 H2). apply H4 in H2.
ap extensionality;eau.

transitivity emptyset.
ap H0. ir;uhg;ir. ap H2;exists x;ee;au.
symmetry. ap H1. ir;uhg;ir. ap H2;exists x;ee;au.
Qed. 

Lemma sow_ordinal : forall p, is_ordinal (sow p).
Proof.
Proof. 
ir. cp (sow_is_sow p). uh H; ee. am.  
Qed. 

Lemma sow_property : forall p,
(exists x:E, (is_ordinal x & p x)) ->
p (sow p).
Proof.
ir. 
cp (sow_is_sow p). uh H0; ee. cp (H1 H).
am.
Qed.

Lemma sow_smallest : forall (p:EP) o,
is_ordinal o -> p o -> sub (sow p) o.
Proof.
ir. 
cp (sow_is_sow p). uh H1; ee.
ap H4. am. am.
Qed. 

Lemma sow_unicity : forall p, unicity (is_sow p).
Proof.
uhg;ir. uh H;uh H0;ee.
apply by_cases with (exists x, is_ordinal x & p x);ir.
cp H7. apply H4 in H7;apply H1 in H8;clear H4;clear H1;clear H2;clear H5.
ap extensionality;au.

assert (forall x, is_ordinal x -> ~ p x). ir. uhg;ir. ap H7;exists x;ee;au.
transitivity emptyset;au. symmetry. au.
Qed.

End Sow.

