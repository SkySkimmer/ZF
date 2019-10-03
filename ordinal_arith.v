Set Implicit Arguments.
Unset Strict Implicit.

Require Export cardinal.
Require Export lci.
Require Export ring.

Module Cardinal_arith.
Export Cardinal.

Lemma singleton_product_l : forall x y, product (singleton x) y = Im (J x) y.
Proof.
ir;ap extensionality;uhg;ir.
apply product_pr in H;ee;nin H.
clpri H0;clpri H1;apply singleton_eq in H0;subst.
ap Im_inc. am.
Im_nin H;subst;ap product_pair_inc;au.
ap singleton_inc.
Qed.

Lemma singleton_product_r : forall x y, product x (singleton y) = Im (fun a => J a y) x.
Proof.
ir;ap extensionality;uhg;ir.
apply product_pr in H;ee;nin H.
clpri H0;clpri H1;apply singleton_eq in H1;subst.
ap Im_show_inc. exists a;ee;au.
Im_nin H;subst;ap product_pair_inc;au.
ap singleton_inc.
Qed.

Definition caPlus c d := card (union2 (product (singleton emptyset) c)
(product (singleton (singleton emptyset)) d)).

Definition caMult c d := card (product c d).

Section NotaSection.

Infix "+" := caPlus.
Infix "*" := caMult.

Lemma caPlus_0eq : forall a b, caPlus a b = emptyset -> (a=emptyset & b=emptyset).
Proof.
ir.
ufi caPlus H.
cp (card_equipotent ((union2 (product (singleton ∅) a) (product (singleton (singleton ∅)) b)))).
rwi H H0. clear H.
nin H0. ee;
ap excluded_middle;uhg;ir;
apply not_empty_nonempty in H0;
nin H0.
apply emptyset_empty with (ev x (J emptyset x0)).
eapply trans_of_map;try am.
ap union2_l;ap product_pair_inc;au.
ap singleton_inc.
apply emptyset_empty with (ev x (J (singleton emptyset) x0)).
eapply trans_of_map;try am.
ap union2_r;ap product_pair_inc;au.
ap singleton_inc.
Qed.


Lemma caPlus_card_proper : forall a a', are_equipotent a a' -> 
forall b b', are_equipotent b b' ->
caPlus a b = caPlus a' b'.
Proof.
ir.
ap card_invariant.
ap Equipotent.union2_equipotent;try ap Equipotent.product_equipotent;
try ap are_equipotent_refl;au.
ap empty_emptyset;ir.
apply inter2_and in H1;ee. apply product_pr in H1;apply product_pr in H2;ee.
apply singleton_eq in H5;apply singleton_eq in H3.
apply emptyset_empty with emptyset. eapply eq_ind.
ap singleton_inc.
wr H3;au.
ap empty_emptyset;ir.
apply inter2_and in H1;ee. apply product_pr in H1;apply product_pr in H2;ee.
apply singleton_eq in H5;apply singleton_eq in H3.
apply emptyset_empty with emptyset. eapply eq_ind.
ap singleton_inc.
wr H3;au.
Qed.

Lemma caPlus_strict_union : forall x y, inter2 x y = emptyset -> 
caPlus x y = card (union2 x y).
Proof.
ir. ap card_invariant.
ap Equipotent.union2_equipotent.
ap empty_emptyset;ir.
apply inter2_and in H0;ee.
apply product_pr in H0;ee;nin H0.
clpri H2;clpri H3.
apply singleton_eq in H2;subst.
apply product_pair_pr in H1;ee.
apply singleton_eq in H0.
apply emptyset_empty with emptyset. eapply eq_ind.
ap singleton_inc. au.
am.
ap are_equipotent_sym. ap trans_equipotent.
exists (J emptyset). uhg;ee;uhg;ir.
ap product_pair_inc;au. ap singleton_inc.
apply pair_eq in H2;au.
apply product_pr in H0;ee;nin H0.
clpri H1;clpri H2;apply singleton_eq in H1;subst.
exists b;ee;au.

ap are_equipotent_sym. ap trans_equipotent.
exists (J (singleton emptyset)). uhg;ee;uhg;ir.
ap product_pair_inc;au. ap singleton_inc.
apply pair_eq in H2;au.
apply product_pr in H0;ee;nin H0.
clpri H1;clpri H2;apply singleton_eq in H1;subst.
exists b;ee;au.
Qed.

Lemma caMult_card_proper : forall a a', are_equipotent a a' -> 
forall b b', are_equipotent b b' ->
caMult a b = caMult a' b'.
Proof.
ir. ap card_invariant. ap Equipotent.product_equipotent;am.
Qed.


Lemma caMult_singleton_l : forall x y, caMult (singleton x) y = card y.
Proof.
ir;ap card_invariant.
ap are_equipotent_sym. ap trans_equipotent.
exists (J x). uhg;ee;uhg;ir.
ap product_pair_inc;au. ap singleton_inc.
apply pair_eq in H1;am.
apply product_pr in H;ee;nin H;clpri H0;clpri H1.
apply singleton_eq in H0;subst.
exists b;ee;au.
Qed.


Lemma caPlus_comm : forall c d, c + d = d + c.
Proof.
ir;uf caPlus.
ap card_invariant.
rw are_equipotent_transformation.
exists (fun x => let a := P x in let b := Q x in if eq_dec a (emptyset) then
J ((singleton emptyset)) b else
J (emptyset) b).

assert (Hs : singleton emptyset <> emptyset).
uhg;ir. apply emptyset_empty with emptyset. eapply eq_ind.
ap singleton_inc. am.

uhg;ee;uhg;ir.
apply union2_or in H. nin H; apply product_pr in H;ee;nin H;
clpri H0;clpri H1;clpr.
apply singleton_eq in H0;subst.
rw eq_dec_if. ap union2_r. ap product_pair_inc. ap singleton_inc.
am.

apply singleton_eq in H0;subst.
rw eq_dec_if_not.
ap union2_l. ap product_pair_inc. ap singleton_inc. am.
am.

apply union2_or in H;apply union2_or in H0.
nin H;nin H0;apply product_pr in H;apply product_pr in H0;ee;nin H;nin H0;
clpri H1;clpri H2;clpri H3;clpri H4;clpri H5;clpr;
apply singleton_eq in H4;apply singleton_eq in H2;
subst;repeat rwi eq_dec_if H1.
apply pair_eq in H1. ap uneq. am.
rwi eq_dec_if_not H1. cp Hs;nin H.
apply pair_eq in H1. au.
cp Hs;nin H. rwi eq_dec_if_not H1. apply pair_eq in H1. am.
am.
rwi eq_dec_if_not H1;au. apply pair_eq in H1. 
nin Hs;ee;au.

rwi eq_dec_if_not H1;au;rwi eq_dec_if_not H1;au.
apply pair_eq in H1. ee;subst. tv. 

apply union2_or in H. nin H;apply product_pr in H;ee;nin H;clpri H0;clpri H1;clpr;
apply singleton_eq in H0;subst.
econstructor. ee. ap union2_r. ap product_pair_inc. ap singleton_inc.
am.
clpr. rw eq_dec_if_not;au.
econstructor. ee. ap union2_l. ap product_pair_inc. ap singleton_inc. am.
clpr. rw eq_dec_if. tv.
Qed.

Lemma caMult_comm : forall c d, c*d=d*c.
Proof.
ir;uf caMult;ap card_invariant.
rw are_equipotent_transformation.
exists (fun x => J (Q x) (P x)).
uhg;ee;uhg;ir.
apply product_pr in H;ee;nin H. clpri H0;clpri H1;clpr.
ap product_pair_inc;au.
apply product_pr in H;ee;nin H. clpri H1;clpri H2;clpri H3.
apply product_pr in H0;ee; nin H. clpri H1.
apply pair_eq in H1. ee;subst;tv.

apply product_pr in H;ee;nin H. clpri H0;clpri H1;clpr.
econstructor;ee. ap product_pair_inc. am. am.
clpr. tv.
Qed.


Lemma caPlus_assoc : forall x y z, caPlus x (caPlus y z) = caPlus (caPlus x y) z.
Proof.
ir. uf caPlus.

assert (Hs : singleton emptyset <> emptyset).
uhg;ir. apply emptyset_empty with emptyset. eapply eq_ind.
ap singleton_inc. am.

ap card_invariant.
rw are_equipotent_transformation.
set (t1:= singleton emptyset). set (t2 := singleton t1).

cp (card_equipotent (union2 (product t1 y) (product t2 z))).
cp (card_equipotent (union2 (product t1 x) (product t2 y))).
apply are_equipotent_sym in H. rwi are_equipotent_transformation H.
rwi are_equipotent_transformation H0.
destruct H as [f H]. destruct H0 as [g H0].

exists (fun p => let a := P p in let b := Q p in 
if eq_dec a emptyset then (*b in x -> g (emptyset, b) in card ...*)
J emptyset (g p )
else let c := f b in
if eq_dec (P c) emptyset then J emptyset (g (J (t1) (Q c)))
else c).
uhg;ee;uhg;ir.
apply union2_or in H1;nin H1;apply product_pr in H1;ee;
nin H1;clpri H2;clpri H3;clpr;apply singleton_eq in H2;subst.
rw eq_dec_if.
ap union2_l. ap product_pair_inc. ap singleton_inc.
ap H0. ap union2_l. ap product_pair_inc. ap singleton_inc. am.
rw eq_dec_if_not;au.
apply H in H3. apply union2_or in H3;nin H3;apply product_pr in H1;ee;
nin H1;clpri H2;clpri H3;clpr;apply singleton_eq in H2;subst.
rw eq_dec_if. ap union2_l. ap product_pair_inc. ap singleton_inc. ap H0.
ap union2_r. ap product_pair_inc. ap singleton_inc. am.
rw eq_dec_if_not;au. ap union2_r. ap product_pair_inc. ap singleton_inc.
am.

apply union2_or in H1;nin H1;apply product_pr in H1;ee;
nin H1;clpri H4;clpri H5;apply singleton_eq in H4;subst;
apply union2_or in H2;nin H2;apply product_pr in H1;ee;nin H1;
clpri H4;clpri H2;apply singleton_eq in H2;subst;clpri H3;repeat rwi eq_dec_if H3.
apply pair_eq in H3;ee.
ap H0. ap union2_l. ap product_pair_inc. ap singleton_inc.
am. ap union2_l. ap product_pair_inc. ap singleton_inc.
am.
am.

apply H in H4. apply union2_or in H4;nin H4; apply product_pr in H1;ee;
nin H1;clpri H2;clpri H4.
rwi eq_dec_if_not H3;au.
clpri H3.
apply singleton_eq in H2;subst. rwi eq_dec_if H3.
apply pair_eq in H3;ee.
apply H0 in H2. apply pair_eq in H2;ee. nin Hs;au.
ap union2_l. ap product_pair_inc. ap singleton_inc.
am.
 ap union2_r. ap product_pair_inc. ap singleton_inc.
am.
rwi eq_dec_if_not H3;au.
clpri H3. apply singleton_eq in H2;subst.
rwi eq_dec_if_not H3;au. apply pair_eq in H3;ee;nin Hs;au.
rwi eq_dec_if_not H3;au.
apply H in H5.
apply union2_or in H5;nin H5;apply product_pr in H1;ee;nin H1;
clpri H2;clpri H5;apply singleton_eq in H2;subst;clpri H3.
rwi eq_dec_if H3.
apply pair_eq in H3;ee.
apply H0 in H2. apply pair_eq in H2;ee;nin Hs;au.
 ap union2_r. ap product_pair_inc. ap singleton_inc.
am.  ap union2_l. ap product_pair_inc. ap singleton_inc.
am.
rwi eq_dec_if_not H3;au. apply pair_eq in H3;ee;nin Hs;au.

ap uneq. ap H. am. am.
apply H in H5;apply H in H4.
apply union2_or in H5;nin H5;apply product_pr in H1;ee;nin H1;
clpri H2;clpri H5;apply singleton_eq in H2;subst;
apply union2_or in H4;nin H4;apply product_pr in H1;ee;nin H1;
clpri H2;clpri H4;apply singleton_eq in H2;subst;clpri H3;
repeat rwi eq_dec_if H3.
rwi eq_dec_if_not H3;au. rwi eq_dec_if_not H3;au.
apply pair_eq in H3. ee.
apply H0 in H2;try (ap union2_r;ap product_pair_inc;try (ap singleton_inc);am).
apply pair_eq in H2;ee.
subst.  tv.
rwi eq_dec_if_not H3;au. rwi eq_dec_if_not H3;au.
rwi eq_dec_if_not H3;au. apply pair_eq in H3;ee;nin Hs;au.
rwi eq_dec_if_not H3;au. rwi eq_dec_if_not H3;au. rwi eq_dec_if_not H3;au.
apply pair_eq in H3;ee;nin Hs;au.
rwi eq_dec_if_not H3;au. rwi eq_dec_if_not H3;au. rwi eq_dec_if_not H3;au.
rwi eq_dec_if_not H3;au.

apply union2_or in H1;nin H1;apply product_pr in H1;ee;nin H1;
clpri H2;clpri H3;clpr;apply singleton_eq in H2;subst.
apply H0 in H3. nin H3;ee.
subst. apply union2_or in H1;nin H1;apply product_pr in H1;ee;
nin H1;clpri H2;clpri H3;apply singleton_eq in H2;subst;clpr.
exists (J emptyset b). ee.
ap union2_l. ap product_pair_inc. ap singleton_inc.
am.
clpr. rw eq_dec_if. tv.
assert (inc (J emptyset b) (union2 (product t1 y) (product t2 z))).
ap union2_l. ap product_pair_inc. ap singleton_inc.
am.
apply H in H1. nin H1;ee;subst.
exists (J t1 x0);ee.
ap union2_r. ap product_pair_inc. ap singleton_inc.
am.
clpr.  rw eq_dec_if_not;au. rw H2;clpr. rw eq_dec_if. tv.
assert (inc (J t1 b) (union2 (product t1 y) (product t2 z))).
ap union2_r. ap product_pair_inc. ap singleton_inc.
am.
apply H in H1;nin H1;ee;subst.
econstructor. ee. ap union2_r. ap product_pair_inc.
ap singleton_inc. am. clpr. rw eq_dec_if_not;au.
rw H2;clpr. rw eq_dec_if_not;au.
Qed.

Lemma caMult_assoc : forall x y z, caMult x (caMult y z) = caMult (caMult x y) z.
Proof.
ir. transitivity (card (product x (product y z))).
ap card_invariant.
ap Equipotent.product_equipotent.
ap are_equipotent_refl.
ap are_equipotent_sym. ap card_equipotent.
etransitivity. ap card_invariant. ap Equipotent.product_equipotent_assoc.
ap card_invariant.
ap Equipotent.product_equipotent.
ap card_equipotent.
ap are_equipotent_refl.
Qed.


Lemma caPlus_cardinal_0_r : forall x, is_cardinal x -> caPlus x emptyset = x.
Proof.
ir. transitivity (card x).
ap card_invariant. rw product_emptyset_r.
ap trans_equipotent.
exists Q. uhg;ee;uhg;ir.
apply union2_or in H0;nin H0. apply product_pr in H0;ee. am.
edestruct emptyset_empty;am.
apply union2_or in H0;apply union2_or in H1.
nin H0;nin H1;try (edestruct emptyset_empty;am).
apply product_pr in H0;apply product_pr in H1. ee.
nin H0;nin H1. clpri H3;clpri H4;clpri H5;clpri H6.
clpri H2. apply singleton_eq in H5;apply singleton_eq in H3;subst;tv.
exists (J emptyset y). ee.
ap union2_l. ap product_pair_inc. ap singleton_inc. am.
clpr;tv.
symmetry;ap cardinal_eq_card. am.
ap are_equipotent_refl.
Qed.


Lemma caPlus_N_0_r : forall x, inc x nNum -> caPlus x emptyset = x.
Proof.
ir. ap caPlus_cardinal_0_r. wr nNum_card. ap card_is_cardinal. am.
Qed.

Lemma caPlus_N_S : forall x, inc x nNum -> forall y, inc y nNum -> 
caPlus x (oS y) = oS (caPlus x y).

Proof.
pose (p := fun x y => inc (caPlus x y) nNum -> caPlus x (oS y) = oS (caPlus x y)).
assert (forall x n, inc x nNum -> inc n nNum -> p x n).
uf p;ir.
symmetry. ap cardinal_eq_card. eapply eq_ind. ap card_is_cardinal.
ap nNum_card. ap oS_nNum;am.

ap are_equipotent_sym. ap trans_equipotent.
cp (card_equipotent (union2 (product (singleton ∅) x)
          (product (singleton (singleton ∅)) n))).
apply are_equipotent_sym in H2.
rwi are_equipotent_transformation H2.
destruct H2 as [f H2].
cp product_pair_inc;cp singleton_inc.
assert (singleton emptyset <> emptyset).
uhg;ir;apply emptyset_empty with emptyset.
eapply eq_ind. ap singleton_inc. am.

assert (forall a, inc a (x+n) -> a<>x+n).
ir. ap ordinal_inc_neq. ap card_ordinal. am.
assert (forall a, a=x+n -> ~ inc a (x+n)).
uhg;ir;subst. eapply H6. am. tv.

exists (fun a => if eq_dec a (x+n) then J (singleton emptyset) n
else f a).
uhg;ee;uhg;ir.
rwi oS_inc H8;nin H8.
rw eq_dec_if_not. apply H2 in H8.
apply union2_or in H8. nin H8.
ap union2_l;am. ap union2_r. apply product_pr in H8.
ee. ap product_inc. am. am. rw oS_inc;au.
ap ordinal_inc_neq. ap card_ordinal. am.
subst. rw eq_dec_if. ap union2_r.
ap product_pair_inc;au. rw oS_inc;au.

rwi oS_inc H8;rwi oS_inc H9.
nin H8;nin H9;subst;repeat rwi eq_dec_if H10.
rwi eq_dec_if_not H10;au. rwi eq_dec_if_not H10;au.
ap H2;au.
subst. rwi eq_dec_if_not H10;au.
apply H2 in H8.
apply union2_or in H8. rwi H10 H8.
nin H8;apply product_pair_pr in H8;ee.
apply singleton_eq in H8. nin H5;am.
edestruct ordinal_inc_neq. ap nNum_ordinal.
ap H0. am. tv.
rwi eq_dec_if_not H10;au.
apply H2 in H9. apply union2_or in H9.
wri H10 H9. nin H9;apply product_pair_pr in H8;ee.
nin H5;ap singleton_eq;am.
edestruct ordinal_inc_neq. ap nNum_ordinal.
ap H0. am. tv.
tv.

apply union2_or in H8. nin H8;apply product_pr in H8;ee;
nin H8;clpri H9;clpri H10;apply singleton_eq in H9;subst.
assert (inc (J emptyset b)  (union2 (product (singleton ∅) x)
          (product (singleton (singleton ∅)) n))).
ap union2_l;au.
apply H2 in H8.
nin H8. ee.
exists x0;ee.
rw oS_inc. left;am.
rw eq_dec_if_not;au.
rwi oS_inc H10. nin H10.
assert (inc (J (singleton emptyset) b)  (union2 (product (singleton ∅) x)
          (product (singleton (singleton ∅)) n))).
ap union2_r;au.
apply H2 in H9.
nin H9. ee.
exists x0;ee.
rw oS_inc. left;am.
rw eq_dec_if_not;au.
subst.
exists (x+n). ee. rw oS_inc;au.
rw eq_dec_if;au.

pose (p' x n := inc (x+n) nNum).
assert (forall x, inc x nNum -> forall n, inc n nNum -> p' x n).
intros x Hx. ap nNum_rect;uf p';ir.
rw caPlus_N_0_r;am.
ufi p H. rw H. ap oS_nNum. am.
am. am. am.

ir;ap H;try am.
ap H0;am.
Qed.

Lemma caPlus_N_lci : is_lci caPlus nNum.
Proof.
uhg. intros x Hx.
ap nNum_rect.
rw caPlus_N_0_r;am.
ir. rw caPlus_N_S;au. ap oS_nNum;am.
Qed.

Lemma caPlus_N_comm : commutative caPlus nNum.
Proof.
uhg;ir;ap caPlus_comm.
Qed.

Lemma caPlus_N_assoc : associative caPlus nNum.
Proof.
uhg;ir;ap caPlus_assoc.
Qed.

Lemma caPlus_N_0_l : forall x, inc x nNum -> caPlus emptyset x = x.
Proof.
ir;etransitivity. ap caPlus_comm.
ap caPlus_N_0_r;am.
Qed.

Lemma caPlus_0_N_neutre : is_neutre caPlus nNum emptyset.
Proof.
uhg;ee. ap emptyset_N. ap caPlus_N_0_r. ap caPlus_N_0_l.
Qed.

Lemma caPlus_N_monoid : is_monoid caPlus nNum emptyset.
Proof.
uhg;ee. ap caPlus_N_lci. ap caPlus_0_N_neutre.
ap caPlus_N_assoc.
Qed.


Lemma caMult_0_r : forall x, caMult x emptyset = emptyset.
Proof.
ir. ap empty_emptyset;ir.
cp (card_equipotent (product x emptyset)).
nin H0. apply H0 in H. nin H;ee.
apply product_pr in H;ee;eapply emptyset_empty;am.
Qed.

Lemma caMult_0_l : forall x, caMult emptyset x = emptyset.
Proof.
ir. rw caMult_comm. ap caMult_0_r.
Qed.

Lemma caMult_singleton_r : forall a x, caMult a (singleton x) = card a.
Proof.
ir. ap card_invariant. ap are_equipotent_sym. ap trans_equipotent.
exists (fun y => J y x).
uhg;ee;uhg;ir. ap product_pair_inc. am. ap singleton_inc.
apply pair_eq in H1;ee;au.
apply product_pr in H;ee;nin H;clpri H0;clpri H1.
apply singleton_eq in H1;subst.
exists a0;ee. am. tv.
Qed.

Lemma caMult_N_o1_r : forall n, inc n nNum -> caMult n o1 = n.
Proof.
ir. rw o1_rw. rw caMult_singleton_r. ap nNum_card. am.
Qed.

Lemma caMult_N_S : forall a, inc a nNum -> forall b, inc b nNum -> 
caMult a (oS b) = caPlus (caMult a b) a.
Proof.
pose (p := fun x y => inc (caMult x y) nNum -> caMult x (oS y) = caPlus (caMult x y) x).
assert (forall a, inc a nNum -> forall b, inc b nNum -> p a b).
uf p;ir.
ap card_invariant.
ap trans_equipotent. 
cp (card_equipotent (product a b)).
rwi are_equipotent_transformation H2.
destruct H2 as [f H2].

assert (singleton emptyset <> emptyset).
uhg;ir;apply emptyset_empty with emptyset.
eapply eq_ind. ap singleton_inc. am.


exists (fun p => let pb := Q p in
if eq_dec pb b then J (singleton emptyset) (P p)
else J emptyset (f p)).
uhg;ee;uhg;ir.
apply product_pr in H4;ee;nin H4.
clpri H5;clpri H6. rwi oS_inc H6.
clpr. nin H6.
rw eq_dec_if_not. ap union2_l. ap product_pair_inc.
ap singleton_inc. ap H2. ap product_pair_inc;am.
ap ordinal_inc_neq;try am. ap nNum_ordinal;am.
subst. rw eq_dec_if. ap union2_r.
ap product_pair_inc. ap singleton_inc. am.

apply product_pr in H4;apply product_pr in H5;ee;nin H4;nin H5.
clpri H9;clpri H10;clpri H7;clpri H8.
clpri H6.
rwi oS_inc H10;rwi oS_inc H8;nin H10;nin H8;subst;repeat rwi eq_dec_if H6.
rwi eq_dec_if_not H6. rwi eq_dec_if_not H6. apply pair_eq in H6;ee.
apply H2;au. ap product_pair_inc;am. ap product_pair_inc;am.
ap ordinal_inc_neq;au. ap nNum_ordinal;am.
ap ordinal_inc_neq;au. ap nNum_ordinal;am.
rwi eq_dec_if_not H6. apply pair_eq in H6;ee.
nin H3;au.
ap ordinal_inc_neq;au. ap nNum_ordinal;am.
rwi eq_dec_if_not H6. apply pair_eq in H6;ee. nin H3;au.
ap ordinal_inc_neq;au. ap nNum_ordinal;am.
apply pair_eq in H6;ee.
subst. tv.

apply union2_or in H4;nin H4;
apply product_pr in H4;ee;nin H4;
clpri H5;clpri H6;apply singleton_eq in H5;subst.
cp H6. apply H2 in H4. nin H4;ee.
subst. apply product_pr in H4;ee;nin H4.
clpri H5;clpri H7.
exists (J a0 b0);ee. ap product_pair_inc. am. rw oS_inc;au.
clpr. rw eq_dec_if_not. tv.
ap ordinal_inc_neq;au. ap nNum_ordinal;am.
exists (J b0 b);ee. ap product_pair_inc;au.
rw oS_inc;au. clpr. rw eq_dec_if;au.

assert (forall a, inc a nNum -> forall b, inc b nNum -> inc (caMult a b) nNum).
intros a Ha. ap nNum_rect;ir.
rw caMult_0_r. ap emptyset_N.
rw H. ap caPlus_N_lci. am. am. am. am. am.

ir;ap H;au.
Qed.

Lemma caMult_N_lci : is_lci caMult nNum.
Proof.
uhg;intros a Ha;ap nNum_rect;ir.
rw caMult_0_r. ap emptyset_N.
rw caMult_N_S. ap caPlus_N_lci. am. am. am. am.
Qed.

Lemma caMult_N_comm : commutative caMult nNum.
Proof.
uhg;ir;ap caMult_comm.
Qed.

Lemma caMult_N_assoc : associative caMult nNum.
Proof.
uhg;ir;ap caMult_assoc.
Qed.

Lemma caMult_1_neutre : is_neutre caMult nNum o1.
Proof.
uhg;ee. ap o1_N. ap caMult_N_o1_r.
ir. rw caMult_comm. ap caMult_N_o1_r;am.
Qed.

Lemma caMult_N_monoid : is_monoid caMult nNum o1.
Proof.
uhg;ee. ap caMult_N_lci.
ap caMult_1_neutre. ap caMult_N_assoc.
Qed.

Lemma caMult_distrib_l : forall a b c, caMult a (caPlus b c) = caPlus
(caMult a b) (caMult a c).
Proof.
ir. transitivity (caPlus (product a b) (product a c)). ap card_invariant.
ap trans_equipotent.
assert (singleton emptyset <> emptyset).
uhg;ir;apply emptyset_empty with emptyset.
eapply eq_ind. ap singleton_inc. am.

cp (card_equipotent (union2 (product (singleton emptyset) b)
(product (singleton (singleton emptyset)) c))).
replace ((card
          (union2 (product (singleton ∅) b)
             (product (singleton (singleton ∅)) c)))) with (b+c) in H0.
Focus 2. tv.
apply are_equipotent_sym in H0.
rwi are_equipotent_transformation H0.
destruct H0 as [f H0].
pose (g := fun p => let pfp := P (f (Q p)) in let qfp := Q (f (Q p)) in
if eq_dec pfp emptyset then J emptyset (J (P p) (qfp))
else J (singleton emptyset) (J (P p) (qfp))).
assert (forall p, inc p (product a (b+c)) -> (Q (g p) = J (P p) (Q (f (Q p))) &  
inc (g p) (union2 (product (singleton ∅) (product a b))
        (product (singleton (singleton ∅)) (product a c))))).
ir.
 ap PropGuard_use. uf g;ee. apply product_pr in H1;ee;nin H1. clpri H2;clpri H3.
clpr. apply H0 in H3. apply union2_or in H3;nin H3;
apply product_pr in H1;ee;nin H1;clpri H3;clpri H4;apply singleton_eq in H3;
ap Pguard;ee;subst;clpr.
rw eq_dec_if. clpr. tv.
rw eq_dec_if. ap union2_l. ap product_pair_inc.
ap singleton_inc. ap product_pair_inc;am.

rw eq_dec_if_not. clpr. tv.
am.
rw eq_dec_if_not;au. ap union2_r.
repeat ap product_pair_inc;au. ap singleton_inc.

exists g.
uhg;ee;uhg;ir.
ap H1. am.

cp (uneq Q H4). rwi (and_P (H1 x H2)) H5.
rwi (and_P (H1 y H3)) H5.
apply pair_eq in H5. ee.
apply product_pr in H2;ee;apply product_pr in H3;ee;nin H2;nin H3;
clpri H7;clpri H8;clpri H9;clpri H10;clpri H4;clpri H5;clpri H6.
cp H8;cp H10;apply H0 in H8. apply H0 in H10.
subst.
ap uneq. apply union2_or in H8;apply union2_or in H10.
clear H1. ufi g H4;clpri H4.
ap H0. am. am.
nin H8;nin H10;apply product_pr in H1;apply product_pr in H5;ee;
nin H1;nin H5;clpri H11;clpri H12;clpri H6;clpri H10;clpri H8;
apply singleton_eq in H11;apply singleton_eq in H8;subst;clpri H4
;repeat rwi eq_dec_if H4;au.
rwi eq_dec_if_not H4;au. apply pair_eq in H4;ee;nin H;au.
rwi eq_dec_if_not H4;au. apply pair_eq in H4;ee;nin H;au.

clear H1.
apply union2_or in H2;nin H2;apply product_pr in H1;ee;nin H1;
clpri H2;clpri H3;apply singleton_eq in H2;subst;clpr.
assert (inc (J emptyset (Q b0))  (union2 (product (singleton ∅) b)
          (product (singleton (singleton ∅)) c))).
ap union2_l;ap product_pair_inc. ap singleton_inc. eapply product_pr. am.
apply H0 in H1. nin H1;ee;subst.
uf g. apply product_pr in H3;ee;nin H3.
clpri H4;clpri H5;clpri H2. exists (J a0 x).
ee. ap product_pair_inc;am.
clpr. rw H2;clpr. rw eq_dec_if. tv.


assert (inc (J (singleton emptyset) (Q b0))  (union2 (product (singleton ∅) b)
          (product (singleton (singleton ∅)) c))).
ap union2_r;ap product_pair_inc. ap singleton_inc. eapply product_pr. am.
apply H0 in H1. nin H1;ee;subst.
uf g. apply product_pr in H3;ee;nin H3.
clpri H4;clpri H5;clpri H2. exists (J a0 x).
ee. ap product_pair_inc;am.
clpr. rw H2;clpr. rw eq_dec_if_not;au.



(*other part of transitivity from very beginning*)
ap caPlus_card_proper; ap card_equipotent.
Qed.

Lemma caMult_distrib_r : forall a b c, caMult (caPlus b c) a = caPlus
(caMult b a) (caMult c a).
Proof.
ir. rw caMult_comm. rw caMult_distrib_l. rw caMult_comm. ap uneq.
ap caMult_comm.
Qed.

Lemma caMult_N_distrib : distributes caPlus caMult nNum.
Proof.
uhg. ee. uhg. ir.
ap caMult_distrib_l.
uhg;ir;ap caMult_distrib_r.
Qed.

Lemma ca_N_quasiring : is_quasiring caPlus caMult nNum emptyset o1.
Proof.
uhg;ee.
ap caPlus_N_monoid.
ap caMult_N_monoid.
ap caMult_N_distrib.
ir;ap caMult_0_l.
ir;ap caMult_0_r.
Qed.

Lemma caMult_integral : forall a b, caMult a b = emptyset -> (a=emptyset \/ b=emptyset).
Proof.
ir;apply by_cases with (a=emptyset);ir;au.
right. ap empty_emptyset;ir.
cp (card_equipotent (product a b)).
ufi caMult H. rwi H H2.
nin H2. assert (nonempty a).
ap not_empty_nonempty.
am.
nin H3.
cp (product_pair_inc H3 H1).
apply (bijective_of_map H2) in H4.
eapply emptyset_empty;am.
Qed.

End NotaSection.

End Cardinal_arith.


Module Ordinal_arith.
Export Ordinal. Export Function.
Export Map.
Import Cardinal_arith.


Definition oPlus b := ordinal_rec_cases b (fun o fo => oS fo) 
(fun h => union (range h)).

Lemma oPlus_0_r : forall b, oPlus b emptyset = b.
Proof.
ir. uf oPlus.
rw ordinal_rec_case_0. tv.
Qed.

Lemma oPlus_S : forall b, forall a, is_ordinal a -> 
oPlus b (oS a) = oS (oPlus b a).
Proof.
ir. uf oPlus.
rw ordinal_rec_case_S. tv. am.
Qed.

Lemma oPlus_limit : forall a, limit_ordinal a -> forall b,
oPlus b a = union (Im (oPlus b) a).
Proof.
ir.
uf oPlus. rw ordinal_rec_case_limit.
rw range_Im_rw. rw create_domain.
ap uneq. fold (oPlus b).
ap Im_ev_create. ap create_axioms.
am.
Qed.

Lemma oPlus_1_r : forall a, oPlus a (oS emptyset) = oS a.
Proof.
ir.  rw oPlus_S. rw oPlus_0_r. tv. ap emptyset_ordinal.
Qed.

Lemma oPlus_inc_compat_r : forall a, forall b c, is_ordinal c -> inc b c -> 
inc (oPlus a b) (oPlus a c).
Proof.
intros a b. pose (H := emptyset). (*dummy value*)
 pose (p := fun c => inc b c -> inc (oPlus a b) (oPlus a c)).
assert (forall c, is_ordinal c -> p c).
ap ordinal_ind_cases;uf p;ir.
apply emptyset_empty in H0;nin H0.

ufi oS H2. rwi tack_on_inc H2. nin H2.
rw oPlus_S. uf oS;rw tack_on_inc;au. am.
subst. rw oPlus_S;au.
uf oS;rw tack_on_inc;au.

rw (oPlus_limit H0).
cp H2. wri (ordinal_limit_union_self H0) H3. apply union_ex in H3;nin H3;ee.
cp (H1 x H3 H4).
ap union_inc. exists (oPlus a x). ee.
ap Im_inc. am. am.

ap H0.
Qed.

Lemma oPlus_ordinal : forall b, is_ordinal b -> forall a, is_ordinal a -> 
is_ordinal (oPlus b a).
Proof.
intros b H. ap ordinal_ind_cases.
rw oPlus_0_r;am.
ir. rw oPlus_S;au. ap ordinal_S;am.
ir. rw oPlus_limit;au.
ap ordinal_union.
ir. apply Im_ex in H2;nin H2;ee;subst;au.
Qed.

Lemma oPlus_sub_compat_l : forall b c, is_ordinal c -> inc b c -> forall a, is_ordinal a -> 
sub (oPlus b a) (oPlus c a).
Proof.
intros b c H H0. assert (is_ordinal b).
apply ordinal_in_ordinal with c;am.
ap ordinal_ind_cases.
rw oPlus_0_r. rw oPlus_0_r.
rw ordinal_sub_leq_of;au;uhg;au.

ir.
repeat rw oPlus_S;au.
cp oPlus_ordinal.
uf oS;uhg;intro;repeat rw tack_on_inc;ir.
nin H5. left. au.
subst. 
rwi ordinal_sub_leq_of H3;au.

ir. rw oPlus_limit;au.
rw oPlus_limit;au.
uhg;ir.
apply union_ex in H4;nin H4;ee.
apply Im_ex in H4;nin H4;ee;subst.
ap union_inc. exists (oPlus c x0). ee.
ap Im_inc;am.
ap H3. am. am.
Qed.

Lemma oPlus_sub_compat_r : forall a, is_ordinal a -> forall b, is_ordinal b -> 
forall c, is_ordinal c -> sub b c -> 
sub (oPlus a b) (oPlus a c).
Proof.
ir. rwi ordinal_sub_leq_of H2;au.
rw ordinal_sub_leq_of.
nin H2. left.
ap oPlus_inc_compat_r. am. am.
subst. right;tv.
ap oPlus_ordinal;am. ap oPlus_ordinal;am.
Qed.

Lemma oPlus_reg_r : forall a, is_ordinal a -> forall b c, is_ordinal b -> is_ordinal c -> 
oPlus a b = oPlus a c -> b=c.
Proof.
ir.
cp (oPlus_ordinal).
destruct ordinal_inc_eq_inc with b c;au.
destruct ordinal_not_inc_self with (oPlus a b).
au. assert (inc (oPlus a b) (oPlus a c)).
ap oPlus_inc_compat_r;au. wri H2 H5;am.
nin H4. am.
destruct ordinal_not_inc_self with (oPlus a c).
au. assert (inc (oPlus a c) (oPlus a b)).
ap oPlus_inc_compat_r;au. rwi H2 H5;am.
Qed.

Lemma oPlus_assoc : forall a, is_ordinal a -> forall b, is_ordinal b -> forall c, is_ordinal c -> oPlus (oPlus a b) c = oPlus a (oPlus b c).
Proof.
intros a Ha b H. ap ordinal_ind_cases.
rw oPlus_0_r. rw oPlus_0_r. tv.
ir. rw oPlus_S. rw oPlus_S. rw oPlus_S.
rw H1. tv. ap oPlus_ordinal;am. am. am.

ir.  rw (oPlus_limit H0).
rw (oPlus_limit H0).
assert (limit_ordinal (⋃ (Im (oPlus b) o))).
uhg;ee. ap ordinal_union.
ir. apply Im_ex in H2;nin H2;ee;subst. ap oPlus_ordinal.
am. apply ordinal_in_ordinal with o;am.
assert (sub (oS emptyset) o).
uhg;ir. ufi oS H2;rwi tack_on_inc H2. nin H2.
apply emptyset_empty in H2;nin H2. subst.
destruct (ordinal_inc_eq_inc) with emptyset o;try am.
ap emptyset_ordinal. nin H2. subst. ap False_rect.
uh H0;ee. nin H2. apply emptyset_empty with x;am.
apply emptyset_empty in H2;nin H2.

exists (oPlus b emptyset).
assert (union o = o). ap ordinal_limit_union_self;am.
assert (inc emptyset o). ap H2;uf oS;rw tack_on_inc;au.
wri H3 H4. apply union_ex in H4;nin H4.
ee.
ap union_inc. econstructor.
ee. ap Im_inc. am. ap oPlus_inc_compat_r. apply ordinal_in_ordinal with o;am.
am.

uhg;ir. nin H2.
ee. assert (inc x (oS x)). uf oS;rw tack_on_inc;au.
wri H3 H4.
apply union_ex in H4. nin H4;ee.
apply Im_ex in H4. nin H4;ee.
subst.
eapply H0. exists x1. assert (is_ordinal x1). apply ordinal_in_ordinal with o;am.
ee. am.
destruct (ordinal_inc_eq_inc) with o (oS x1).
am. ap ordinal_S;am.
ufi oS H7;rwi tack_on_inc H7;nin H7. destruct ordinal_inc_inc_not with o x1;au.
subst. destruct ordinal_not_inc_self with x1;au.
nin H7. am. 
assert (inc (oS x) (union (Im (oPlus b) o))).
ap union_inc. econstructor. ee.
ap Im_inc. am. rw oPlus_S;au.
ap ordinal_S_inc_inc. am. ap oPlus_ordinal;au.
am.
rwi H3 H8. destruct ordinal_not_inc_self with (oS x);au.
ap ordinal_S;am.


assert (oPlus b o = union (Im (oPlus b) o)).
ap oPlus_limit. am.

wr oPlus_limit;au. wr oPlus_limit;au.
assert (oPlus (oPlus a b) o = union (Im (oPlus (oPlus a b)) o)).
ap oPlus_limit;au. rw H4.
assert (⋃ (Im (oPlus (oPlus a b)) o) = (union (Im (fun d => oPlus a (oPlus b d)) o))).
ap uneq. ap Im_uneq. ir. au. rw H5.
transitivity (union (Im (oPlus a) (oPlus b o))).
Focus 2. symmetry. ap oPlus_limit. rw H3;am.

assert (forall y, inc y ((Im (fun d : E => oPlus a (oPlus b d)) o)) -> is_ordinal y).
ir. apply Im_ex in H6. nin H6. ee. subst. ap oPlus_ordinal;try am.
ap oPlus_ordinal;try am. apply ordinal_in_ordinal with o;am.
assert (forall y, inc y ( (Im (oPlus a) (oPlus b o))) -> is_ordinal y).
ir. apply Im_ex in H7;nin H7;ee;subst. ap oPlus_ordinal. am.
eapply ordinal_in_ordinal. Focus 2. am. ap oPlus_ordinal;try am. ap H0.
ap extensionality;[idtac | ap ordinal_union_sub;try am;ir].

uhg;ir. apply union_ex in H8;ee;nin H8;ee.
ap union_inc;exists x;ee;try am.
apply Im_ex in H8. nin H8;ee;subst.
ap Im_inc. 
rw H3. assert (inc (oS x0) o). ap ordinal_limit_gt. am. am.
ap union_inc;econstructor;ee. ap Im_inc. am. rw oPlus_S. uf oS;rw tack_on_inc;au.
apply ordinal_in_ordinal with o;try am. ap H0.

apply Im_ex in H8. nin H8;ee;subst.
rwi H3 H8. apply union_ex in H8;nin H8;ee.
apply Im_ex in H8;nin H8;ee;subst.
assert (inc (oPlus a x) (oPlus a (oPlus b x1))).
ap oPlus_inc_compat_r. ap oPlus_ordinal. am. apply ordinal_in_ordinal with o. 
ap H0. am.
am.
exists (oPlus a (oPlus b x1)). ee.
ap Im_show_inc. exists x1;ee. am. tv.
assert (is_ordinal a). am. assert (is_ordinal b). am.
assert (is_ordinal o). ap H0. assert (is_ordinal x1).
apply ordinal_in_ordinal with o;am.
assert (is_ordinal (oPlus b x1)). ap oPlus_ordinal. am. am.
assert (is_ordinal x). apply ordinal_in_ordinal with (oPlus b x1);am.
cp (oPlus_ordinal). rw ordinal_sub_leq_of;au.
uhg. au.
Qed.

Lemma oPlus_sub_l : forall a, is_ordinal a -> forall b, is_ordinal b -> 
sub a (oPlus a b).
Proof.
intros a H. ap ordinal_ind_cases.
rw oPlus_0_r. ap sub_refl.
ir. uhg;ir. rw oPlus_S;au. uf oS;rw tack_on_inc;au.

ir.
rw (oPlus_limit H0).
uhg;ir. ap union_inc.
uh H0;ee. nin H3.
cp (H1 x H3).
cp ( H5  a0 H2).
econstructor. ee. ap Im_inc. am. am.
Qed.

Lemma oPlus_sub_r : forall a, is_ordinal a -> forall b, is_ordinal b -> 
sub b (oPlus a b).
Proof.
intros a H. ap ordinal_ind_cases.
ap emptyset_sub_all.
ir. 
rw oPlus_S;au. uf oS;uhg;ir. rwi tack_on_inc H2. nin H2.
rw tack_on_inc. left. au.
rw tack_on_inc;subst. rwi ordinal_sub_leq_of H1;au.
ap oPlus_ordinal;au.

ir.
uhg;ir.
assert (inc (oS a0) o). ap ordinal_limit_gt;am.
apply H1 in H3.
rw oPlus_limit;try am. ap union_inc.
econstructor. ee. ap Im_inc. ap ordinal_limit_gt. am. am.
ap H3. uf oS;rw tack_on_inc;au.
Qed.

Lemma oPlus_0_l : forall a, is_ordinal a -> oPlus emptyset a = a.
Proof.
ap ordinal_ind_cases.
ap oPlus_0_r.
ir. rw oPlus_S. ap uneq. am. am.
ir. rw oPlus_limit;au.
ap extensionality;uhg;ir.
apply union_ex in H1;nin H1;ee. apply Im_ex in H1;nin H1;ee;subst.
rwi H0 H2. uh H;ee;uh H;ee;eapply H;am.
am.
ap union_inc.
econstructor. ee. ap Im_inc. ap ordinal_limit_gt;am.
rw H0. uf oS;rw tack_on_inc;au. ap ordinal_limit_gt;au.
Qed.

Lemma oPlus_caPlus_N_eq : forall x, inc x nNum -> forall y, inc y nNum -> 
oPlus x y = caPlus x y.
Proof.
intros x Hx;ap nNum_rect.
rw oPlus_0_r. rw caPlus_N_0_r. tv. am.
ir. rw oPlus_S. rw caPlus_N_S. ap uneq. am.
am. am. ap nNum_ordinal;am.
Qed.

Lemma ordinal_sub_ex : forall a, is_ordinal a -> forall b, is_ordinal b -> 
sub a b -> exists c, is_ordinal c & b = oPlus a c.
Proof.
intros a H.
pose (p := fun a b => exists c, is_ordinal c & b = oPlus a c).
assert (forall b, is_ordinal b -> sub a b -> p a b);try am.
ap ordinal_sub_ind;uf p;ir. am.

exists emptyset;ee. ap emptyset_ordinal. rw oPlus_0_r;au.

destruct H2 as [c H2].
ee.
exists (oS c);ee. ap ordinal_S. am. subst.
symmetry. ap oPlus_S. am.

(*limit ordinal case*)
pose (n := union (Z b (fun x => inc (oPlus a x) b))).
assert (forall x, is_ordinal x -> inc (oPlus a x) b -> inc x b).
ir.
assert (sub x (oPlus a x)). ap oPlus_sub_r. am. am.
eapply ordinal_sub_inc_trans. am. am.
am. am.

assert (forall x, is_ordinal x -> inc (oPlus a x) b -> inc x (Z b (fun y => inc (oPlus a x) b))).
ir;ap Z_inc;au.

assert (b = union (Z b (sub a))).
ap extensionality. uhg;ir.
assert (is_ordinal a0). apply ordinal_in_ordinal with b;am.
ap union_inc. 
destruct ordinal_inc_eq_inc with a a0;try am.
exists (oS a0). ee. ap Z_inc. ap ordinal_limit_gt. am. am.
cp (ordinal_S H6). uh H8;ee.
ap H8. clear H8;clear H9;clear H10.
apply ordinal_inc_trans with a0;try am.
rw oS_inc;au.
ap ordinal_S;am.
rw oS_inc;au.
nin H7;subst.
exists (oS a0). ee.
ap Z_inc. ap ordinal_limit_gt. am. am.
uhg;ir;rw oS_inc;au.
rw oS_inc;au.

exists a;ee. ap Z_inc. am. ap sub_refl.
am.

uhg;ir. union_nin H5. apply Z_all in H5;ee.
assert (is_transitive_set b). am. eapply H8.
am. am.

exists n;ee. uf n. ap ordinal_union. ir.
apply Z_sub in H6. apply ordinal_in_ordinal with b;am.
etransitivity. am.
transitivity (union (Im (oPlus a) n)).
ap uneq. ap extensionality;uhg;ir.
apply Z_all in H6;ee.
ap Im_show_inc. destruct H2 with a0.
am. am. ee.
exists x. ee;au. ap union_inc. exists (oS x).
ee. ap Z_inc. ap ordinal_limit_gt;try am. ap H3.
am. wr H9. am.
rw oPlus_S;au. ap ordinal_limit_gt;try am. wr H9. am.
rw oS_inc;au.
Im_nin H6. 
rw H7.
union_nin H6. apply Z_all in H6. ee.
ap Z_inc. apply ordinal_inc_trans with (oPlus a x0).
ap oPlus_inc_compat_r. apply ordinal_in_ordinal with b;am.
am. am. am.
ap oPlus_sub_l. am.
apply ordinal_in_ordinal with x0;try am. apply ordinal_in_ordinal with b;try am.

assert (limit_ordinal n).
uhg;ee. ap ordinal_union. ir.
apply Z_sub in H6. apply ordinal_in_ordinal with b;am.
uf n. econstructor. ap union_inc. econstructor;ee.
ap Z_inc. Focus 2. rw oPlus_S. rw oPlus_0_r. ap ordinal_limit_gt. am. am.
ap emptyset_ordinal. ap ordinal_limit_gt. am.
ap ordinal_nonempty_emptyset_inc. am. am.
rw oS_inc;right;tv.
uhg;ir. nin H6. ee.
assert (inc (oS x) n).
uf n. assert (inc x n). rw H7. rw oS_inc;au.
union_nin H8.
apply Z_all in H8. ee.
ap union_inc. exists (oS x0). ee.
ap Z_inc. ap ordinal_limit_gt;am.
rw oPlus_S;au. ap ordinal_limit_gt;am.
apply ordinal_in_ordinal with b;am.
ap ordinal_S_inc_inc. am.
apply ordinal_in_ordinal with b;am.
am.
rwi H7 H8. apply ordinal_not_inc_self with (oS x). 
ap ordinal_S;am. am.
rw (oPlus_limit H6).
tv.
Qed.

Lemma ordinal_sub_ex_rw : forall a, is_ordinal a -> forall b, is_ordinal b -> 
sub a b = (exists c, is_ordinal c & b = oPlus a c).
Proof.
ir;ap iff_eq.
ap ordinal_sub_ex. am. am.
ir;nin H1;ee;subst.
ap oPlus_sub_l. am. am.
Qed.


Definition oMult a := ordinal_rec_cases emptyset (fun b fb => oPlus (fb) a)
(fun h => union ( range h)).

Lemma oMult_0_r : forall a, oMult a emptyset = emptyset.
Proof.
ir. ap ordinal_rec_case_0.
Qed.

Lemma oMult_S : forall a b, is_ordinal b -> oMult a (oS b) = oPlus (oMult a b) a.
Proof.
ir.
ap ordinal_rec_case_S. am.
Qed.

Lemma oMult_limit : forall a b, limit_ordinal b -> oMult a b = union (Im (oMult a) b).
Proof.
ir. etransitivity. ap ordinal_rec_case_limit. am.
rw create_range. reflexivity.
Qed.

Lemma oMult_1_r : forall a, is_ordinal a -> oMult a o1 = a.
Proof.
uf o1. ir.
rw oMult_S. rw oMult_0_r. rw oPlus_0_l. tv. am.
ap emptyset_ordinal.
Qed.

Lemma oMult_nNum_repeat : forall a, is_ordinal a -> 
forall n, inc n nNum -> oMult a n = nNum_repeat (fun x => oPlus x a) n emptyset.
Proof.
intros a H. ap nNum_rect.
rw oMult_0_r. rw nNum_repeat_0. tv.
ir.
rw oMult_S.
rw nNum_repeat_S. wr H1.
tv. am. ap nNum_ordinal;am.
Qed.

Definition oExp a := ordinal_rec_cases o1 (fun b fb => oMult fb a)
(fun h => union (range h)).
(*oExp a b = a^b*)

Lemma oExp_0_r : forall a, oExp a emptyset = o1.
Proof.
ir. ap ordinal_rec_case_0.
Qed.

Lemma oExp_S : forall a b, is_ordinal b -> oExp a (oS b) = oMult (oExp a b) a.
Proof.
ir. ap ordinal_rec_case_S. am.
Qed.

Lemma oExp_limit : forall a b, limit_ordinal b -> oExp a b = union (Im (oExp a) b).
Proof.
ir. etransitivity. ap ordinal_rec_case_limit. am.
rw create_range. tv.
Qed.



Section Order_types.

Definition union_order (ra : E2P) (a : E) (rb : E2P) (b : E) (x y : E) :=
(inc x a & inc y a & ra x y)\/(inc x a & inc y b)\/(inc x b & inc y b & rb x y).

Lemma union_order_wo : forall ra a, is_well_order ra a ->
forall rb b, is_well_order rb b -> 
inter2 a b = emptyset -> 
is_well_order (union_order ra a rb b) (union2 a b).
Proof.
ir. uhg;dj.
uhg;ee;uhg;ir;try uhg.

apply union2_or in H2;nin H2.
left. ee;au. ap H. am.
right;right. ee;au. ap H0;am.

uh H4;uh H5;repeat nin H4;repeat nin H5;ee.
ap H;au.
destruct emptyset_empty with x. wr H1.
ap inter2_inc;am.
edestruct emptyset_empty. wr H1.
ap inter2_inc;am.
destruct emptyset_empty with y. wr H1.
ap inter2_inc;am.
edestruct emptyset_empty. wr H1.
ap inter2_inc;am.
edestruct emptyset_empty. wr H1.
ap inter2_inc;am.
edestruct emptyset_empty. wr H1.
ap inter2_inc;am.
destruct emptyset_empty with y. wr H1.
ap inter2_inc;am.
ap H0;am.

repeat nin H4;repeat nin H6;ee.
left. ee;au. apply H with y;am.
right;left;ee;au.
right;left;ee;au.
destruct emptyset_empty with y. wr H1.
ap inter2_inc;am.
right;left;au.
right;left;au.
destruct emptyset_empty with y. wr H1.
ap inter2_inc;am.
destruct emptyset_empty with y. wr H1.
ap inter2_inc;am.
right;right;ee;au;apply H0 with y;am.


apply by_cases with (exists x, inc x b0 & inc x a);ir.
nin H5;ee.
assert (ex (is_min a ra (inter2 a b0))).
ap H. ap inter2_l. exists x;ap inter2_inc;am.
nin H7. exists x0.
uhg;ee. uhg;ee.
ap union2_l;am.
ir. cp (H3 x1 H8).
apply union2_or in H9. nin H9.
uhg. left. ee;au.
ap H7. ap inter2_inc;am.
right. left. ee;am.
eapply inter2_r. am.

assert (sub b0 b).
uhg;ir. cp (H3 a0 H6).
apply union2_or in H7;nin H7.
nin H5;exists a0;ee;am. am.
assert (ex (is_min b rb b0)).
ap H0. 
am. am.
nin H7. exists x;uhg;ee;try uhg;ee.
ap union2_r;am.
ir.
right;right. ee;au.
ap H7;au.
am.
Qed.

Lemma union_order_l : forall ra a rb b, inter2 a b = emptyset -> 
forall x,  forall y, inc y a -> 
union_order ra a rb b x y -> (A (ra x y) (inc x a)).
Proof.
ir. nin H1. ee;am.
nin H1. edestruct emptyset_empty;ee;wr H. ap inter2_inc.
ap H0. am.
edestruct emptyset_empty;wr H. ap inter2_inc.
ap H0. am.
Qed.

Lemma union_order_r : forall ra a rb b, inter2 a b = emptyset -> forall x y, inc x b -> 
union_order ra a rb b x y -> (A (rb x y) (inc y b)).
Proof.
ir.
nin H1. destruct emptyset_empty with x;wr H;ap inter2_inc;am.
nin H1. destruct emptyset_empty with x;wr H;ap inter2_inc;am.
ee;am.
Qed.


Lemma union_order_m : forall ra a rb b x, inc x a -> forall y, inc y b -> union_order ra a rb b x y.
Proof.
ir;uhg;au.
Qed.

(*
Lemma oPlus_union_order_isomorphic : forall ra a, is_well_order ra a -> 
forall rb b, is_well_order rb b -> 
inter2 a b = emptyset -> 
are_rel_isomorphic (union_order ra a rb b) (union2 a b) sub (oPlus (oType ra a) (oType rb b)).
Proof.
pose (prop := fun ra a o => forall rb b, is_well_order rb b -> o = oType rb b -> inter2 a b = emptyset -> 
are_rel_isomorphic (union_order ra a rb b) (union2 a b) sub (oPlus (oType ra a) (oType rb b))).
assert (forall ra a, is_well_order ra a -> forall o, is_ordinal o ->
prop ra a o).
Focus 2.
ir.
ufi prop H. apply H with (oType rb b). am. ap oType_ordinal.
am. tv. am.
intros ra a Ha.
cp (oType_wo_pr Ha).
destruct H as [fa Hfa].
assert (Hfa' : is_isomorphism ra a sub (oType ra a) (inverse fa)).
ap isomorphism_inverse. uhg;ee. ap sub_is_order. ap well_order_total.
ap ordinal_sub_wo.
ap oType_ordinal.
am. am.

ap ordinal_ind_cases;uf prop;clear prop;ir.

(*case 0*)
wr H0. rw oPlus_0_r.
assert (b = emptyset). ap empty_emptyset;ir.
cp (oType_wo_pr H). nin H3. apply H3 in H2. nin H2;ee.
wri H0 H2. eapply emptyset_empty;am.
subst. rw union2_emptyset_r.
exists (inverse fa). uhg;ee;try am.
uhg;ee;try am. ir.
nin H4. ee. ap Hfa'. am. am. am.
nin H4;ee;edestruct emptyset_empty;am.

(*case S*)
assert (exists bm, exists b', b = tack_on b' bm & is_well_order rb b' & ~inc bm b' & 
(forall x, inc x b' -> rb x bm) & o = oType rb b').
cp (oType_wo_pr H1). wri H2 H4.
nin H4. exists (ev x o). exists (Im (ev x) o).
dj. ap extensionality;uhg;ir.
apply H4 in H5.
nin H5;ee;rwi oS_inc H5. subst.
rw tack_on_inc.
nin H5. left. ap Im_inc;am.
right. ap uneq;am.
rwi tack_on_inc H5;nin H5. Im_nin H5;subst.
eapply trans_of_map;try am. rw oS_inc;au.
subst. eapply trans_of_map;try am. rw oS_inc;au.
eapply sub_wellorder. am. rw H5. uhg;ir;rw tack_on_inc;au.
uhg;ir. Im_nin H7.
assert (x0<>o). ap ordinal_inc_neq. am. am.
ap H9. ap H4. rw oS_inc;au. rw oS_inc;au. au.
Im_nin H8;subst.
ap H4;try (rw oS_inc;au).
ap H. am.
ap oType_eq. am. am.
ap are_rel_iso_sym. ap well_order_total_order. ap ordinal_sub_wo. am.
am. exists (L o (ev x)).
uhg;ee. uhg;ee. ap map_of_trans.
uhg;ir. ap Im_inc;am.
ir. rw create_ev;au. rw create_ev;au. assert (sub o (oS o)).
uhg;ir;rw oS_inc;au. ap H4;au.
ap map_of_bijective.
assert (sub o (oS o)). uhg;ir;rw oS_inc;au.
uhg;ee. uhg;ir;ap Im_inc;am.
uhg;ir. ap H4;au.
uhg;ir. Im_nin H10;subst. exists x0;ee;au.

destruct H4 as [bm H4]. destruct H4 as [b' H4]. ee.
subst.
destruct H0 with rb b' as [f H'].
am. tv. ap empty_emptyset. ir.
apply inter2_and in H4;ee.
apply emptyset_empty with y. wr H3.
ap inter2_inc. am. rw tack_on_inc;au.
clear H0.
wr H2. rw oPlus_S. Focus 2. ap oType_ordinal.
exists (tack_on f (J bm (oPlus (oType ra a) (oType rb b')))).
uf oS. rw union2_tack_on_r.

assert (forall x, inc x a -> x<>bm).
uhg;ir;subst. apply emptyset_empty with bm. wr H3.
ap inter2_inc. am. rw tack_on_inc;au.
assert (forall x, inc x b' -> x<>bm).
uhg;ir;subst;au.
assert (Hubm : ~ inc bm (union2 a b')).
uhg;ir. apply union2_or in H8;nin H8.
eapply H0;au. eapply H4;au.

uhg;ee. uhg;ee. ap tack_on_map. am.
uhg;ir. apply union2_or in H8;nin H8.
destruct H0 with bm. am. tv.
destruct H4 with bm;au.

ir.
nin H10. ee.
clear H8;clear H9.
rw (map_tack_on_ev (and_P (and_P H'))).
rw (map_tack_on_ev (and_P (and_P H'))).
ap H';au. ap union2_l. am. ap union2_l. am.
left. ee;am.
uhg;ir. apply union2_or in H8;nin H8.
eapply H0;au. eapply H4;au.
ap union2_l. am. am.
ap union2_l. am.
clear H8;clear H9. 
repeat rwi tack_on_inc H10.
nin H10;ee.
rw (map_tack_on_ev (and_P (and_P H'))).
nin H9. rw (map_tack_on_ev (and_P (and_P H'))).
ap H';au. ap union2_l;am. ap union2_r;am.
right;left;ee;am.
am. ap union2_r;am.
subst. rw (map_tack_on_ev_eq (and_P (and_P H'))).
ap oPlus_ordinal. ap oType_ordinal. ap oType_ordinal.
eapply trans_of_map. am. ap union2_l;am.
am. am. ap union2_l;am.
nin H8;nin H9;subst.
rw (map_tack_on_ev (and_P (and_P H'))).  rw (map_tack_on_ev (and_P (and_P H'))).
ap H'. ap union2_r;am. ap union2_r;am.
right;right;ee;am.
am. ap union2_r;am. am.
ap union2_r;am.
rw (map_tack_on_ev (and_P (and_P H'))).
rw (map_tack_on_ev_eq (and_P (and_P H'))).
ap oPlus_ordinal. ap oType_ordinal. ap oType_ordinal.
eapply trans_of_map. am. ap union2_r;am.
am. am. ap union2_r;am.
destruct H4 with y. am.
ap H1. rw tack_on_inc;au. rw tack_on_inc;au.
ap H7. am. am.
ap sub_refl.

ap tack_on_bijective.
am. am.
ap ordinal_not_inc_self. ap oPlus_ordinal;ap oType_ordinal.


(*limit case*)
subst.
assert (forall b', sub b' b -> inc (oType rb b') (oType rb b) -> 
are_rel_isomorphic (union_order ra a rb b') (union2 a b') sub
       (oPlus (oType ra a) (oType rb b'))).
ir. eapply H0. am. eapply sub_wellorder.
am. am. tv. ap empty_emptyset;ir.
apply inter2_and in H5;ee;apply emptyset_empty with y.
wr H3. ap inter2_inc;au.
clear H0.
assert ( Hie : forall b', sub b' b -> inter2 a b'  = emptyset).
ir. ap empty_emptyset;ir.
apply inter2_and in H4;ee;apply emptyset_empty with y.
wr H3. ap inter2_inc;au.

assert (forall b', sub b' b -> inc (oType rb b') (oType rb b) -> 
oPlus (oType ra a) (oType rb b') = oType (union_order ra a rb b') (union2 a b')).
ir.
ap oType_eq.
ap union_order_wo. am. apply sub_wellorder with b.
am. am. au. ap oPlus_ordinal;ap oType_ordinal.
au.
rw (oPlus_limit H).
replace (oPlus (oType ra a)) with (fun o => oPlus (oType ra a) o).
Focus 2. ap arrow_extensionality. ir;tv.
(*
need something to say that forall x, inc x b -> 
inc (oType rb (Z b (fun y => lt_of rb y x))) (oType rb b)
*)


Qed.
*)


End Order_types.



End Ordinal_arith.

