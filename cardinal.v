Set Implicit Arguments.
Unset Strict Implicit.

Require Export ordinals.

Module Enumerator.
Export Ordinal. Export Function.
Export Map.

Definition chooser f a := forall x, sub x a -> nonempty x -> inc (f x) x.

Definition enumerator f a := forall o, is_ordinal o -> 
nonempty (complement a (Im f o)) -> inc (f o) (complement a (Im f o)).

Section VarSec.

Variables (chooseF : E1) (a : E).

Hypothesis (chooseH : chooser chooseF a).

Definition enumerator_of := ordinal_rec (fun h => 
chooseF (complement a (Im (ev h) (domain h)))).

Lemma enum_of_enum : enumerator (enumerator_of) a.
Proof.
uhg;ir. uf enumerator_of.
rw ordinal_rec_pr;try am.
rw create_domain.
fold enumerator_of.
rw Im_ev_create. ap chooseH.
ap Z_sub. am.
Qed.

End VarSec.

Section VarSec2.

Variables (a : E) (enum : E1).

Hypothesis (Henum : enumerator enum a).

Lemma enumeration_ends : exists o, is_ordinal o & sub a (Im enum o).
Proof.
ap excluded_middle;uhg;ir.
assert (forall o, is_ordinal o -> nonempty (complement a (Im enum o))).
ir. ap excluded_middle;uhg;ir.
ap H. exists o;ee;au.
uhg;ir. ap excluded_middle;uhg;ir.
ap H1;exists a0;ap Z_inc;au.
assert (forall o, is_ordinal o -> inc (enum o) (complement a (Im enum o))).
ir. ap Henum. am. au.
assert (forall o, is_ordinal o -> forall o', inc o' o -> enum o <> enum o').
ir. uhg;ir.
assert (is_ordinal o'). apply ordinal_in_ordinal with o;am.
cp H2;cp H5. apply H1 in H6;apply H1 in H7.
apply Z_all in H6;ee.
rwi H4 H8. ap H8. ap Im_inc. am.
assert (forall o o', is_ordinal o -> is_ordinal o' -> enum o = enum o' -> o = o').
ir. destruct ordinal_inc_eq_inc with o o';au.
destruct H2 with o' o;au. nin H6. am.
destruct H2 with o o';au.

pose (r := fun x y => (is_ordinal y & x = enum y) \/ (~(exists o, is_ordinal o & x= enum o) & y=emptyset)).
assert ((forall x, ex (r x) & (unicity (r x)))).
ir;ee. apply by_cases with (exists o, is_ordinal o & x = enum o);ir.
nin H4. ee. exists x0. uf r. left. ee;au.
exists emptyset. right. ee;au.
uhg;ir. nin H4;nin H5. ee.
ap H3;au. wr H7;am.
ee. subst. nin H5. exists y;au.
ee;subst;nin H4;exists y';au.
ee;subst;tv.
pose (z := replacement r a).
apply ordinal_not_set. exists z;ir.
uf z. ap replacement_inc. uhg. am. exists (enum o);ee.
eapply Z_sub;ap H1. am.
uf r. left. ee;au.
Qed.

Definition l := Sow.sow (fun x => sub a (Im enum x)).

Lemma l_ordinal : is_ordinal l.
Proof.
ap Sow.sow_ordinal.
Qed.

Lemma l_pr : sub a (Im enum l).
Proof.
uf l. ap Sow.sow_property. ap enumeration_ends.
Qed.

Lemma l_smallest : forall o, is_ordinal o -> sub a (Im enum o) -> sub l o.
Proof.
uf l. ap Sow.sow_smallest.
Qed.

Lemma l_inc_cmp : forall o, inc o l -> inc (enum o) (complement a (Im enum o)).
Proof.
ir. ap Henum.
apply ordinal_in_ordinal with l;au. ap l_ordinal.
ap excluded_middle;uhg;ir.
cp H. cp l_ordinal;cp (ordinal_in_ordinal l_ordinal H).
rwi ordinal_inc_not_sub H1;au.
ap H1. ap l_smallest. am. uhg;ir;ap excluded_middle;uhg;ir;ap H0.
exists a0;ap Z_inc;au.
Qed.

Lemma l_Im_eq : a = Im enum l.
Proof.
ap extensionality. ap l_pr.
uhg;ir.
apply Im_ex in H. nin H;ee. subst.
eapply Z_sub. ap l_inc_cmp. am. 
Qed.

Lemma l_enum_inj : Application.injects l enum.
Proof.
assert (forall x y, inc x y -> inc y l -> enum x = enum y -> x=y).
ir.
assert (inc x l). cp l_ordinal.
uh H2;ee;eapply H2;am.
cp (l_inc_cmp H0).
apply Z_pr in H3. nin H3. wr H1. ap Im_inc;am.
uhg;ir.
assert (is_ordinal x & is_ordinal y).
cp l_ordinal. ee;eapply ordinal_in_ordinal;am. ee.
destruct ordinal_inc_eq_inc with x y;au. nin H5;au.
symmetry. au.
Qed.

Lemma enum_ends_at_l : Application.bijective l a enum.
Proof.
uhg;ee. uhg;ir.
rw l_Im_eq. ap Im_inc;am.
ap l_enum_inj.
rw l_Im_eq. uhg;ir.
apply Im_ex in H. nin H;exists x;ee;au.
Qed.

Inductive enumr : E2P := 
  | enumr_ir : forall x y, inc x l -> inc y l -> sub x y -> enumr (enum x) (enum y)
.

Lemma enumr_wo : is_well_order enumr a.
Proof.
uhg;ee. uhg;ee.
uhg;ee. ir.
apply enum_ends_at_l in H. nin H;ee;subst.
constructor. am. am. ap sub_refl.
uhg;ir.
inversion H1;subst;inversion H2;subst.
assert (x=y0). ap enum_ends_at_l;au.
subst. assert (y=x0).
ap enum_ends_at_l;au. subst.
ap uneq. ap extensionality;am.

uhg;ir.
inversion H1;subst;inversion H3;subst.
apply enum_ends_at_l in H7;au.
subst.
constructor;au. apply sub_trans with y0;am.

ir.
pose (z := Z l (fun x => inc (enum x) b)).
assert (nonempty z). nin H0.
cp H0. apply H in H1;apply enum_ends_at_l in H1;au. nin H1;ee.
subst. exists x0;ap Z_inc;au.
cp l_ordinal. uh H2. ee.
apply H4 in H1. nin H1.
exists (enum x). uh H1;ee.
apply Z_all in H5;ee.
clear H2;clear H3;clear H4.
uhg;ee;au. uhg;ee. au.
ir. cp H2.
apply H in H3. apply enum_ends_at_l in H3. nin H3;ee;subst.
constructor. am. am.
rw ordinal_sub_leq_of;try (apply ordinal_in_ordinal with l;try ap l_ordinal;try am).
ap H1. ap Z_inc;au. uf z. ap Z_sub.
Qed.

Lemma enum_rel_iso : is_isomorphism sub l enumr a (L l enum).
Proof.
assert (bijective l a (L l enum)).
ap map_of_bijective. ap enum_ends_at_l.
uhg;ee;au. uhg;ee;try am.
ir. rw create_ev;try am. rw create_ev;try am. constructor;am.
Qed.

End VarSec2.

Lemma all_wo : forall a, exists r, is_well_order r a.
Proof.
ir;econstructor. ap enumr_wo.
ap enum_of_enum.
uhg;ir. ap rep_inc. am.
Qed.

Section VarSec3.

Variables (r : E2P) (a : E).

Hypothesis (Hwo : is_well_order r a).

Definition chooseLeast x := unique_choose (is_min a r x).
(*note that we could use union (Z a (is_min a r x)) instead, this is just simpler*)

Lemma chooseLeast_chooses : chooser chooseLeast a.
Proof.
uhg;ir. uf chooseLeast.
cp Hwo. uh H1;ee.
cp (H2 x H H0).
apply unique_choose_pr in H3. am.
ap min_unicity. am.
Qed.

Definition enumLeast := enumerator_of chooseLeast a.

Lemma enumLeast_enum : enumerator enumLeast a.
Proof.
ap enum_of_enum. ap chooseLeast_chooses.
Qed.

Definition lLeast := l a enumLeast.

Lemma lLeast_ordinal : is_ordinal lLeast.
Proof.
ap l_ordinal.
Qed.

Lemma enumLeast_ends_at : Application.bijective lLeast a enumLeast.
Proof.
ap enum_ends_at_l. ap enumLeast_enum.
Qed.

Lemma enumLeast_pr : forall o, inc o lLeast -> 
is_min a r (complement a (Im enumLeast o)) (enumLeast o).
Proof.
ir.
uf enumLeast. uf enumerator_of.
assert (is_ordinal o).
apply ordinal_in_ordinal with lLeast. ap lLeast_ordinal. am.
rw ordinal_rec_pr;try am.
rw create_domain. rw Im_ev_create.
uf chooseLeast. ap unique_choose_pr.
ap Hwo. ap Z_sub.
replace ((ordinal_rec
           (fun h : E =>
            unique_choose (is_min a r (complement a (Im (ev h) (domain h))))))) with
enumLeast. Focus 2. reflexivity.
exists (enumLeast o). ap l_inc_cmp.
ap enumLeast_enum. am.
ap min_unicity. am.
Qed.

Definition enumrLeast := enumr a enumLeast.

Lemma enumrLeast_eq_r : forall x y, inc x a -> inc y a -> r x y = enumrLeast x y.
Proof.
ir;ap iff_eq;ir.
cp H;cp H0. apply enumLeast_ends_at in H2. apply enumLeast_ends_at in H3.
nin H2;nin H3;ee;subst.
assert (is_ordinal x0 & is_ordinal x1). ee;apply ordinal_in_ordinal with lLeast;try am;
ap lLeast_ordinal. ee.
constructor;try am.
rw ordinal_sub_not_inc;try am.
uhg;ir.
cp (enumLeast_pr H2). cp (enumLeast_pr H3).
assert (r (enumLeast x1) (enumLeast x0)).
ap H8. ap Z_inc. am.
uhg;ir. Im_nin H9.
assert (inc x lLeast). cp lLeast_ordinal.
uh H11;ee;eapply H11;am.
apply enumLeast_ends_at in H10;au.
subst. apply ordinal_inc_inc_not with x x1;au.
assert (x1=x0). ap enumLeast_ends_at. am. am.
ap Hwo. am. am. am. am. subst.
apply lLeast_ordinal with x0. am. am.

nin H1.
fold lLeast in *.
cp (enumLeast_pr H1). cp (enumLeast_pr H2). 
ap H4. ap Z_inc;au.
uhg;ir. Im_nin H6.
assert (inc x0 lLeast). cp lLeast_ordinal.
uh H8;ee. apply H8 with x. am. am.
apply enumLeast_ends_at in H7;au.
subst. 
assert (is_ordinal x & is_ordinal x0).
ee;apply ordinal_in_ordinal with lLeast;try am;ap lLeast_ordinal.
ee. rwi ordinal_sub_not_inc H3;au.
Qed.

Lemma enumLeast_isomorphism : is_isomorphism sub lLeast r a (L lLeast enumLeast).
Proof.
assert (bijective lLeast a (L lLeast enumLeast)).
ap map_of_bijective. ap enumLeast_ends_at.
uhg;ee;try am. uhg;ee;try am.
ir. rw create_ev;try am;rw create_ev;try am.
rw enumrLeast_eq_r.
cp (enum_rel_iso enumLeast_enum).
uh H3;ee;uh H3;ee.
fold lLeast in *.
apply H5 in H2;try am.
clear H5.
rwi create_ev H2;try am. rwi create_ev H2;try am.
ap enumLeast_ends_at. am.
ap enumLeast_ends_at. am.
Qed.

End VarSec3.

Lemma wo_iso_ordinal : forall r a, is_well_order r a -> exists o, is_ordinal o & 
are_rel_isomorphic sub o r a.
Proof.
ir. econstructor. ee. ap lLeast_ordinal.
econstructor. ap enumLeast_isomorphism. am.
Qed.

Lemma all_ordinal_equipotent : forall x, exists o, is_ordinal o & are_equipotent x o.
Proof.
ir. cp (all_wo x). nin H.
apply wo_iso_ordinal in H. nin H. ee.
exists x1;ee. am. nin H0.
ap are_equipotent_sym;exists x2. am.
Qed.

Lemma bijective_enum : forall a d f, is_ordinal d -> Application.bijective d a f -> 
enumerator f a.
Proof.
ir. uhg;ee. ir.
assert (inc o d).
rw ordinal_inc_not_sub;au. uhg;ir.
nin H2. apply Z_all in H2;ee.
cp H2. apply H0 in H5.
nin H5;ee;subst.
ap H4. ap Im_inc;au.
ap Z_inc. ap H0. am.
uhg;ir. Im_nin H4.
assert (inc x d). uh H;ee;eapply H;am.
apply H0 in H5;au.
subst. eapply H1;am. 
Qed.

End Enumerator.



Module Ordinal_WO.
Export Ordinal. Import Function. Export Map.
Import Enumerator.


Lemma initial_iso_image : forall r a r' b h (Ht : is_total_order r a) (Ho : is_order r' b),
 is_isomorphism r a r' b h -> 
forall i, is_initial_segment r a i -> is_initial_segment r' b (Im (ev h) i).
Proof.
ir. uhg;ee. uhg;ir. apply Im_ex in H1;nin H1. ee.
subst. uh H;ee;uh H;ee. eapply trans_of_map. ap H. ap H0;am.
ir. apply Im_ex in H2;nin H2;ee;subst.
apply H in H1. nin H1;ee;subst.
ap Im_show_inc. exists x1. ee.
apply H0 with x0. am. am.
eapply total_injective_leq_back. am. am. am. am.
am. ap H0;am. am. tv.
Qed.


Definition oType r a := lLeast r a.

Lemma oType_ordinal : forall r a, is_ordinal (oType r a).
Proof.
ir. uf oType. ap Sow.sow_ordinal.
Qed.

Lemma oType_wo_pr : forall r a, is_well_order r a -> are_rel_isomorphic sub (oType r a) r a.
Proof.
ir.
uf oType. econstructor. ap enumLeast_isomorphism. am.
Qed.

Lemma oType_wo_pr_sym : forall r a, is_well_order r a -> are_rel_isomorphic r a sub (oType r a).
Proof.
ir. ap are_rel_iso_sym. ap ordinal_sub_total.
ap oType_ordinal. am.
ap oType_wo_pr;am.
Qed.

Lemma oType_eq_iso : forall r a r' a', is_well_order r a -> is_well_order r' a' -> 
oType r a = oType r' a' -> are_rel_isomorphic r a r' a'.
Proof.
ir. apply are_rel_iso_trans with sub (oType r a).
ap are_rel_iso_sym. ap ordinal_sub_total. ap oType_ordinal. am.
ap oType_wo_pr. am.
rw H1. ap oType_wo_pr. am.
Qed.

Lemma iso_oType_eq : forall r a r' a', is_well_order r a -> is_well_order r' a' -> 
are_rel_isomorphic r a r' a' -> oType r a = oType r' a'.
Proof.
ir. ap ordinal_isomorphic_unicity.
ap oType_ordinal. ap oType_ordinal.
apply are_rel_iso_trans with r a. ap oType_wo_pr. am.
apply are_rel_iso_trans with r' a'. am.
ap oType_wo_pr_sym. am.
Qed.

Lemma oType_equipotent : forall r a, is_well_order r a -> are_equipotent a (oType r a).
Proof.
ir. apply oType_wo_pr_sym in H.
nin H. exists x. am.
Qed.

Lemma oType_eq : forall ra a, is_well_order ra a -> forall o, is_ordinal o -> 
are_rel_isomorphic ra a sub o -> o = oType ra a.
Proof.
ir. eapply ordinal_isomorphic_unicity. am. ap oType_ordinal.
eapply are_rel_iso_trans. ap are_rel_iso_sym. Focus 3. am.
ap well_order_total_order. am.
ap sub_is_order.
ap oType_wo_pr_sym. am.
Qed.

Definition oIsomorphism r a := L (oType r a) (enumLeast r a).

Lemma oIso_pr : forall r a, is_well_order r a -> is_isomorphism sub (oType r a) r a (oIsomorphism r a).
Proof.
ap enumLeast_isomorphism.
Qed.

Lemma oIso_inverse_pr : forall r a, is_well_order r a -> is_isomorphism r a sub (oType r a) (inverse (oIsomorphism r a)).
Proof.
ir. ap isomorphism_inverse.
uhg;ee. ap sub_is_order. ap well_order_total.
ap ordinal_sub_wo. ap oType_ordinal.
am.
ap oIso_pr. am.
Qed.

End Ordinal_WO.

Module Cardinal.
Export Ordinal_WO. Export Function.
Import Enumerator.

Definition card x := Sow.sow (are_equipotent x).

Lemma card_uf : forall x, card x = Sow.sow (are_equipotent x).
Proof.
ir;reflexivity.
Qed.

Lemma card_ordinal : forall x, is_ordinal (card x).
Proof.
ir;uf card;ap Sow.sow_ordinal.
Qed.

Lemma card_equipotent : forall x, are_equipotent x (card x).
Proof.
ir. uf card. ap Sow.sow_property.
ap all_ordinal_equipotent.
Qed.

Lemma card_smallest : forall x y, is_ordinal y -> are_equipotent x y -> sub (card x) y.
Proof.
ir. uf card. ap Sow.sow_smallest. am. am.
Qed.

Lemma card_invariant : forall x y, are_equipotent x y -> card x = card y.
Proof.
ir.
ap extensionality; uf card; ap Sow.sow_smallest.
ap Sow.sow_ordinal.
wr card_uf.
apply are_equipotent_trans with y. am. ap card_equipotent.
ap Sow.sow_ordinal.
wr card_uf.
apply are_equipotent_trans with x. ap are_equipotent_sym. am.
 ap card_equipotent.
Qed.

Lemma card_eq_iso : forall x y, card x = card y -> are_equipotent x y.
Proof.
ir. apply are_equipotent_trans with (card x).
ap card_equipotent. rw H;ap are_equipotent_sym;
ap card_equipotent.
Qed.

Lemma card_iso_rw : forall x y, are_equipotent x y = (card x = card y).
Proof.
ir;ap iff_eq. ap card_invariant. ap card_eq_iso.
Qed.


Lemma card_sub_oType : forall r a, is_well_order r a -> sub (card a) (oType r a).
Proof.
ir. ap card_smallest. ap oType_ordinal.
ap oType_equipotent. am.
Qed.

Definition is_cardinal c := A (is_ordinal c) 
(forall b, inc b c -> ~ are_equipotent  b c).

Lemma cardinal_equipotent_sub : forall c, is_cardinal c = (A (is_ordinal c) 
(forall b, is_ordinal b -> are_equipotent b c -> sub c b)).
Proof.
ir;ap iff_eq;ir;ee.
am.
ir. rw ordinal_sub_not_inc. uhg;ir.
eapply H. am. am.
am. am.

uhg;ee. am.
ir. uhg;ir.
cp H1. rwi ordinal_inc_not_sub H3.
ap H3. ap H0.
apply ordinal_in_ordinal with c;am.
am. 
apply ordinal_in_ordinal with c;am.
am.
Qed.

Lemma finite_ordinal_cardinal : forall o, finite_ordinal o -> is_cardinal o.
Proof.
ir. uhg;ee. am.
ir.
uhg;ir.
apply are_equipotent_sym in H1.
apply finite_ordinal_equipotent_eq in H1.
subst.  eapply H;am.
am.
apply ordinal_in_ordinal with o;am.
Qed.

Lemma omega_cardinal : is_cardinal nNum.
Proof.
uhg;ee. ap omega_ordinal.
ir.
uhg;ir.
apply finite_ordinal_equipotent_eq in H0. subst.
apply ordinal_not_inc_self with nNum. ap omega_ordinal.
am.
ap nNum_finite_ordinals. am.
ap omega_ordinal.
Qed.

Lemma card_sub_iso_sub : forall x y, sub (card x) (card y) -> iso_sub x y.
Proof.
ir.
assert (are_equipotent x (card x)). ap card_equipotent.
cp (card_equipotent y).
apply are_equipotent_sym in H1.
nin H0;nin H1.
assert (Application.injective x y (fun a => ev x1 (ev x0 a))).
uhg;ee. uhg;ir.
eapply trans_of_map. am. eapply trans_of_map. uhg;ee;try am.
uh H0;ee;ap H0. eapply sub_trans;am.
am.
uhg;ir. apply H1 in H4;au. apply H0 in H4;au.
ap H. eapply trans_of_map;am. 
ap H. eapply trans_of_map;am.
rw iso_sub_rw. exists (create x (fun a : E => ev x1 (ev x0 a))).
ap map_of_injective. am.
Qed.

Lemma iso_sub_card_sub : forall x y, iso_sub x y -> sub (card x) (card y).
Proof.
ir. destruct (ordinal_sub_sub) with (card x) (card y);try am.
ap card_ordinal. ap card_ordinal.
apply card_sub_iso_sub in H0.
assert (card x = card y). ap card_invariant.
ap cantor_bernstein. am. am.
rw H1. ap sub_refl.
Qed.

Lemma sub_card_sub : forall x y, sub x y -> sub (card x) (card y).
Proof.
ir. ap iso_sub_card_sub. ap sub_iso_sub. am.
Qed.

Lemma card_sub_rw : forall x y, (sub (card x) (card y)) = (iso_sub x y).
Proof.
ir;ap iff_eq. ap card_sub_iso_sub. ap iso_sub_card_sub.
Qed.

Lemma card_is_cardinal : forall x, is_cardinal (card x).
Proof.
ir. rw cardinal_equipotent_sub. ee.
ap card_ordinal.
ir.
ap card_smallest. am. apply are_equipotent_trans with (card x).
ap card_equipotent. ap are_equipotent_sym. am. 
Qed.

Lemma card_of_cardinal : forall c, is_cardinal c -> card c = c.
Proof.
ir;ap extensionality.
ap card_smallest.
am. ap are_equipotent_refl.
rwi cardinal_equipotent_sub H. ee.
ap H0. ap card_ordinal. ap are_equipotent_sym.
ap card_equipotent.
Qed.

Lemma nNum_card : forall x, inc x nNum -> card x = x.
Proof.
ir. ap card_of_cardinal. ap finite_ordinal_cardinal.
 ap nNum_finite_ordinals. am.
Qed.

Lemma card_of_card : forall x, card (card x) = card x.
Proof.
ir. ap card_of_cardinal. ap card_is_cardinal.
Qed.

Lemma cardinal_eq_card : forall x c, is_cardinal c -> are_equipotent x c -> 
c = card x.
Proof.
ir. wr (card_of_cardinal H). ap card_invariant. ap are_equipotent_sym;am.
Qed.

Lemma cardinal_equipotent_eq : forall c, is_cardinal c -> forall c', is_cardinal c' -> 
are_equipotent c c' -> c=c'.
Proof.
ir. etransitivity. ap cardinal_eq_card. am. ap are_equipotent_sym.
am. ap card_of_cardinal. am.
Qed.

Lemma card_nNum : forall n, inc n nNum -> card n = n.
Proof.
ir. ap card_of_cardinal.
ap finite_ordinal_cardinal. ap nNum_finite_ordinals. am.
Qed.

Lemma card_ex_gt : forall a, is_cardinal a -> 
exists b, is_cardinal b & inc a b.
Proof.
ir. exists (card (powerset a)).
ee. ap card_is_cardinal.

assert (Hs : iso_sub_strict a (powerset a)).
uhg;ee. rw iso_sub_rw.
exists (L a (fun x => singleton x)).
ap map_of_injective. uhg;ee;uhg;ir.
ap powerset_inc. uhg;ir.
apply singleton_eq in H1;subst;au.
ap singleton_eq. wr H2. ap singleton_inc.
uhg;ir. eapply Application.cantor_strong.
nin H0. exists (ev x).
ap surjective_of_map. rwi bijective_rw H0. am.
assert (iso_sub_strict a (card (powerset a))).
uhg;ee.
apply iso_sub_trans with (powerset a).
am.
exists (card (powerset a)). ee.
ap card_equipotent. ap sub_refl.
uhg;ir. ap Hs.
apply are_equipotent_trans with (card (powerset a)).
am. ap are_equipotent_sym. ap card_equipotent.

wr ordinal_inc_lt_of.
uhg;ee.
apply sub_trans with (card a).
rw card_of_cardinal. ap sub_refl. am.
ap iso_sub_card_sub.
am.
uhg;ir.
ap H0.
wr H1.
ap are_equipotent_refl.
am.
ap card_ordinal.
Qed.

End Cardinal.



Module WO_rec.
Import Enumerator.
Export Cardinal.

Section VarSec.

Variables (r : E2P) (a : E).

Hypothesis (Hwo : is_well_order r a).

Variable (g : E1).

Notation iso := (oIsomorphism r a). (*iso : from oType to a*)

Definition wo_rec x := (ordinal_rec (fun h => 
let h' := compose h (inverse iso) in g h') (ev (inverse iso) x)).

Lemma wo_rec_pr : forall x, inc x a -> wo_rec x = g (L (Z a (fun y => lt_of r y x)) wo_rec).
Proof.
ir.
cp (oIso_pr Hwo).
cp (oIso_inverse_pr Hwo).
uf wo_rec. rw ordinal_rec_pr.
ap uneq.
assert (domain
  (compose
     (L (ev (inverse iso) x)
        (ordinal_rec (fun h : E => g (compose h (inverse iso)))))
     (inverse iso)) =
domain
  (L (Z a (fun y : E => lt_of r y x))
     (fun x0 : E =>
      ordinal_rec (fun h : E => g (compose h (inverse iso)))
        (ev (inverse iso) x0)))).
rw create_domain. rw compose_domain.
rw create_domain.
ap extensionality;uhg;ir.
apply Z_all in H2;ee.
assert (domain (inverse iso) = a). assert (is_map a (oType r a) (inverse iso)).
am. am.
rwi H4 H2.
assert (Application.axioms a (oType r a) (ev (inverse iso))). ap trans_of_map.
am.
cp (H5 x H). cp (H5 a0 H2).
clear H5. assert (is_ordinal (oType r a)). ap oType_ordinal.
cp (ordinal_in_ordinal H5).
wri ordinal_inc_lt_of H3;au.
nin H3.
ap Z_inc;au.
uhg;ee.
assert (is_total_order r a). uhg;ee. am. ap well_order_total;am.
rw (leq_not_lt H10);au.
uhg;ir. nin H11.
ap H9. ap extensionality;au.
ap H1;au.
uhg;ir. ap H9. ap uneq. am.
apply Z_all in H2;ee.
nin H3.
ap Z_inc. eapply eq_ind. am. symmetry.
assert (is_map a (oType r a) (inverse iso));am.

assert (Application.axioms a (oType r a) (ev (inverse iso))). ap trans_of_map.
am.
cp (H5 x H). cp (H5 a0 H2).
clear H5. assert (is_ordinal (oType r a)). ap oType_ordinal.
cp (ordinal_in_ordinal H5).
wr ordinal_inc_lt_of;au. uhg;ee.
ap H1;au. uhg;ir.
ap H4. ap H1;au.


 ap function_extensionality.
ap compose_axioms. ap create_axioms.
am.
ir.
rwi create_domain H2. rwi H2 H3.
rw create_ev;au.
rw compose_ev. rw create_ev. tv.
Focus 2. rw H2. am.

clear H2;apply Z_all in H3;ee.
assert (Application.axioms a (oType r a) (ev (inverse iso))). ap trans_of_map.
am.
cp (H4 x H). cp (H4 x0 H2).
clear H4. assert (is_ordinal (oType r a)). ap oType_ordinal.
cp (ordinal_in_ordinal H4).
wr ordinal_inc_lt_of;au. uhg;ee.
ap H1;au. uhg;ir.
ap H3. ap H1;au.

apply ordinal_in_ordinal with (oType r a).
ap oType_ordinal.
eapply trans_of_map. am. am.
Qed.


End VarSec.

Lemma wo_iso_wo : forall ra a, is_well_order ra a -> forall rb b, is_order rb b -> 
are_rel_isomorphic ra a rb b -> is_well_order rb b.
Proof.
ir.
nin H1.
uhg;ee. am.
ir.
assert (is_total_order ra a). uhg;ee. am.
ap well_order_total. am.
cp (isomorphism_inverse H4 H0 H1).
clear H4.
pose (z := Im (ev (inverse x)) b0). assert (nonempty z).
nin H3. econstructor;ap Im_inc;am.
apply H in H4.
nin H4.
exists (ev x x0).
uh H4;ee. Im_nin H6. subst.
uhg;ee. uhg;ee.
eapply trans_of_map;try am.
ir. assert (x0 = ev x (ev (inverse x) x0)).
symmetry. eapply bijective_inverse_ev_r. am. au.
rw H8. ap H1. am. eapply trans_of_map;try am.
au.
ap H4. ap Im_inc. am.
erewrite bijective_inverse_ev_r. am. am. au.
uhg;ir.
Im_nin H6;subst.
eapply trans_of_map;try am. au.
Qed.
(*nb : rb,b must be order otherwise rb = always true allows any bijection*)

Lemma wo_iso_ev : forall ra a, is_well_order ra a -> forall rb b, is_well_order rb b -> 
forall f, is_isomorphism ra a rb b f -> 
forall x, inc x a -> ev f x = chooseInf b rb (complement b (Im (ev f) (Z a (fun y => lt_of ra y x)))).
Proof.
ir.
assert (sub (complement b (Im (ev f) (Z a (fun y : E => lt_of ra y x)))) b).
ap Z_sub.
assert (nonempty (complement b (Im (ev f) (Z a (fun y : E => lt_of ra y x))))).
ap excluded_middle;uhg;ir.
assert (inc (ev f x) b). eapply trans_of_map;am.
assert (inc (ev f x) (Im (ev f) (Z a (fun y : E => lt_of ra y x)))).
ap excluded_middle;uhg;ir.
ap H4. exists (ev f x);ap Z_inc;am.
Im_nin H6.
apply Z_all in H6;ee.
ap H8.
ap H1;au.

apply H0 in H4;try ap Z_sub.
assert (is_min b rb (complement b (Im (ev f) (Z a (fun y : E => lt_of ra y x))))
(chooseInf b rb (complement b (Im (ev f) (Z a (fun y : E => lt_of ra y x)))))).
ap chooseInf_min. am. am.
eapply min_unicity. Focus 3. am.
am. clear H4;clear H5. clear H3. uhg;ee. uhg;ee.
eapply trans_of_map;am.
ir. apply Z_all in H3;ee.
cp H3. apply H1 in H5. nin H5;ee;subst.
ap H1;au.
erewrite leq_not_lt.
Focus 2. uhg;ee. am. ap well_order_total. am.
uhg;ir. ap H4. ap Im_inc. ap Z_inc.
am. am.
am. am.

ap Z_inc. eapply trans_of_map;am.
uhg;ir.
Im_nin H3.
apply Z_all in H3. ee.
ap H5. ap H1;au.
Qed.

Lemma wo_iso_ev_pr : forall ra a, is_well_order ra a -> forall rb b, is_well_order rb b -> 
forall f, is_isomorphism ra a rb b f -> 
forall x, inc x a -> is_min b rb (complement b (Im (ev f) (Z a (fun y => lt_of ra y x)))) (ev f x).
Proof.
ir.
rw (wo_iso_ev H H0 H1 H2).
ap chooseInf_min. am.
ap H0. ap Z_sub.
exists (ev f x).
ap Z_inc. eapply trans_of_map;am.
uhg;ir. Im_nin H3. apply Z_all in H3;ee.
ap H5. ap H1;au.
Qed.

Lemma wo_only_isomorphism : forall ra a, is_well_order ra a -> forall rb b, is_well_order rb b -> 
unicity (is_isomorphism ra a rb b).
Proof.
ir.
 uhg. ir.
ap function_extensionality;try am.
transitivity a. cp (and_P H1). am.
symmetry. cp (and_P H2). am.
assert (domain y = a). cp (and_P H1). am.
rw H3. clear H3.
ap (wo_ind H).
ir.
rw (wo_iso_ev H H0 H1);au. rw (wo_iso_ev H H0 H2);au.
ap uneq. ap uneq. ap Im_uneq. ir.
apply Z_all in H5;ee. au.
Qed.

Lemma wo_iso_initial : forall ra a, is_well_order ra a -> 
forall rb b, is_well_order rb b -> forall a', is_initial_segment ra a a' -> 
forall b', is_initial_segment rb b b' -> forall f, is_isomorphism ra a rb b f -> 
forall f', is_isomorphism ra a' rb b' f' -> 
sub f' f.
Proof.
ir.
nin H1. nin H2.
eapply map_sub. am. ap H1. am.
cp (sub_wellorder H H1).
ap (wo_ind H7). ir.
assert (forall y, inc y a -> lt_of ra y x -> inc y a').
ir. eapply H5. am. am. am.
assert (forall y, inc y a -> lt_of ra y x -> ev f y = ev f' y).
ir;au.
cp (wo_iso_ev_pr H H0 H3 (H1 x H8)).
cp (wo_iso_ev_pr H7 (sub_wellorder H0 H2) H4 H8).
eapply min_unicity. Focus 2. am. am.
uhg;ee. uhg;ee.
ap H2. am.

ir. apply by_cases with (inc x0 b');ir.
ap H13. ap Z_inc. am.
uhg;ir. Im_nin H16. subst.
apply Z_all in H14;ee.
apply Z_all in H16;ee.
ap H17. wr H9;au.
ap Im_inc. ap Z_inc. au. am.
assert (forall y, inc y b' -> lt_of rb y x0).
ir. apply Z_all in H14;ee.
erewrite lt_not_leq. uhg;ir. ap H15. eau.
uhg;ee. am. ap well_order_total;am. au. am.
destruct H16 with (ev f' x). am. am.

ap Z_inc. ap H2;am. uhg;ir.
Im_nin H14. apply Z_all in H14;ee.
rwi H11 H15;try am.
assert (x = x0).
ap H4. am.
eau. am. subst.
ap H16. tv.
Qed.

Lemma isomorphism_iso_initial_to_initial : forall ra a, is_total_order ra a -> 
forall rb b, is_order rb b -> forall f, is_isomorphism ra a rb b f -> 
forall x, is_initial_segment ra a x -> is_initial_segment rb b (Im (ev f) x).
Proof.
ir. uhg;ee. uhg;ir. Im_nin H3.
subst. eapply trans_of_map;try am. ap H2. am.
ir. Im_nin H4;subst.

cp H3. apply H1 in H6. nin H6;ee;subst.
assert (ra x2 x1).
cp (isomorphism_inverse H H0 H1).
assert (bijective a b f). am. apply bijective_inverse_of in H8.
uh H8;ee. clear H8;clear H9.
uh H10;ee.
assert (inc x1 a). ap H2. am.
wr (H8 x1 H10).
wr (H8 x2 H6).
ap H7. am. eapply trans_of_map;try am.
am.
ap Im_inc. apply H2 with x1. am. am. am.
Qed.



End WO_rec.



Module Finite.
Export Function. Export Map.
Export Ordinal. Export Cardinal.
Import WO_rec.

Inductive is_finite : EP :=
  | finite_emptyset : is_finite emptyset
  | finite_tack_on : forall x, is_finite x -> forall y, is_finite (tack_on x y)
.

Lemma nNum_finite : forall n, inc n nNum -> is_finite n.
Proof.
ap nNum_rect;ir.
ap finite_emptyset.
ap finite_tack_on. am.
Qed.

Lemma finite_nNum_equipotent : forall x, is_finite x -> exists n, inc n nNum & are_equipotent x n.
Proof.
ir;nin H.
exists emptyset;ee. ap emptyset_N. ap are_equipotent_refl.

destruct IHis_finite as [n H0]. ee.
apply by_cases with (inc y x);ir.
exists n. ee. am.
ap are_equipotent_sym. eapply eq_ind. ap are_equipotent_sym;am.
ap extensionality_rw;ir;rw tack_on_inc;ap iff_eq;ir;au.
nin H3;subst;au.
exists (oS n);ee. ap oS_nNum. am.

uf oS . wr tack_on_equipotent. am.
am. ap ordinal_not_inc_self;ap nNum_ordinal;am.
Qed.

Lemma finite_card_nNum : forall x, is_finite x -> inc (card x) nNum.
Proof.
ir. apply finite_nNum_equipotent in H.
nin H;ee.
assert (card x = x0).
symmetry. ap cardinal_eq_card.
wr nNum_card. ap card_is_cardinal. am.
am.
rw H1. am.
Qed.

Lemma finite_invariant : forall x, is_finite x -> forall y, are_equipotent x y -> is_finite y.
Proof.
intros x Hx. nin Hx;ir.
eapply eq_ind. ap finite_emptyset.
symmetry;ap empty_emptyset;ir.
nin H. apply H in H0. nin H0;ee;eapply emptyset_empty;am.
apply by_cases with (inc y x);ir.
assert (tack_on x y = x).
ap extensionality_rw;ir;rw tack_on_inc;ap iff_eq;ir;au.
nin H1;subst;au.
rwi H1 H. au.

rwi are_equipotent_transformation H. destruct H as [ f H ].
assert (y0 = tack_on (Im f x) (f y)).
ap extensionality;uhg;ir.
rw tack_on_inc.
apply H in H1. nin H1;ee. rwi tack_on_inc H1;nin H1;subst;au.
left;ap Im_inc;am.
rwi tack_on_inc H1;nin H1;subst.
Im_nin H1. subst. ap H. rw tack_on_inc. au.
ap H;rw tack_on_inc;au.
subst.
ap finite_tack_on.
ap IHHx.
ap trans_equipotent. exists f.
uhg;ee;uhg;ir.
ap Im_inc;am.
ap H;au;rw tack_on_inc;au.
Im_nin H1. exists x0;ee;au.
Qed.


Lemma card_nNum_finite : forall x, inc (card x) nNum -> is_finite x.
Proof.
ir. apply finite_invariant with (card x).
ap nNum_finite. am.
ap are_equipotent_sym;ap card_equipotent.
Qed.

Lemma finite_equipotent_inj_bij_trans : forall x, is_finite x -> forall y, are_equipotent x y -> 
forall f, Application.injective x y f -> Application.bijective x y f.
Proof.
intros x Hx;nin Hx;ir.
nin H.
uhg;ee;au. uhg;ir.
apply H in H1. nin H1. ee;edestruct emptyset_empty;am.

apply by_cases with (inc y x);ir.
assert (tack_on x y = x).
ap extensionality_rw;ir;rw tack_on_inc;ap iff_eq;ir;au.
nin H2;subst;au.
rw H2. ap IHHx.
rwi H2 H. am. rwi H2 H0. am.

assert (exists z, y0 = tack_on z (f y) & ~inc (f y) z).
exists (Z y0 (fun z => z <> f y));ee.
ap extensionality;uhg;ir.
rw tack_on_inc. apply by_cases with (a=f y);ir;au.
left;ap Z_inc;am.
rwi tack_on_inc H2;nin H2;subst.
apply Z_all in H2. am.
ap H0. rw tack_on_inc;au.
uhg;ir. apply Z_pr in H2. au.
destruct H2 as [z H2].
ee;subst.
wri tack_on_equipotent H;au.
assert (Application.injective x z f).
uhg;ee;uhg;ir.
assert (inc x0 (tack_on x y)). rw tack_on_inc;au.
apply H0 in H4. rwi tack_on_inc H4;nin H4;au.
apply H0 in H4. subst.
nin H1;am.
rw tack_on_inc;au. rw tack_on_inc;au.
ap H0;au;rw tack_on_inc;au.

apply IHHx in H2;au.
assert (forall x0, inc x0 x -> f x0 <> f y).
uhg;ir. apply H0 in H5;subst;au;rw tack_on_inc;au.

uhg;ee;au.
uhg;ir. rwi tack_on_inc H5;nin H5;subst.
apply H2 in H5. nin H5;ee;subst.
exists x0;ee;au. rw tack_on_inc;au.
exists y;ee;au. rw tack_on_inc;au.
Qed.

Lemma finite_inj_bij_trans : forall x, is_finite x -> 
forall f, Application.injective x x f -> Application.bijective x x f.
Proof.
intros x Hx. ap finite_equipotent_inj_bij_trans. am.
ap are_equipotent_refl.
Qed.

Lemma finite_equipotent_inj_bij : forall x, is_finite x -> forall y, are_equipotent x y -> 
forall f, injective x y f -> bijective x y f.
Proof.
ir.
cp (injective_of_map H1).
apply finite_equipotent_inj_bij_trans in H2;au.
uhg;ee;au.
Qed.

Lemma finite_inj_bij : forall x, is_finite x -> 
forall f, injective x x f -> bijective x x f.
Proof.
ir. ap finite_equipotent_inj_bij. am. ap are_equipotent_refl. am.
Qed.

Lemma finite_inj_bij_contra : forall x, ~is_finite x -> exists f, injective x x f & ~bijective x x f.
Proof.
ir.
assert (sub nNum (card x)).
rw ordinal_sub_not_inc. uhg;ir.
ap H. ap card_nNum_finite. am.
ap omega_ordinal. ap card_ordinal.

cp (card_equipotent x).
destruct H1 as [f H1].
cp (bijective_inverse_bijective H1).
cp (bijective_inverse_of H1).
uh H3;ee. clear H3;clear H4.
cp (bijective_inverse_compose_l H1).
cp (bijective_inverse_compose_r H1).
assert (exists g, injective (card x) (card x) g & ~bijective (card x) (card x) g).
exists (L (card x) (fun y => by_cases
(fun _ : inc y nNum => oS y)
(fun _ : ~inc y nNum => y))).
ee. ap map_of_injective.
uhg;ee;uhg;ir. apply by_cases with (inc x0 nNum);ir.
rw by_cases_if;au. ap H0. ap oS_nNum;am.
rw by_cases_if_not;au.
apply by_cases with (inc x0 nNum);ir;apply by_cases with (inc y nNum);ir.
rwi by_cases_if H8;au. rwi by_cases_if H8;au.
apply oS_N_inj in H8;au.
rwi by_cases_if H8;au. rwi by_cases_if_not H8;au.
subst. nin H10. ap oS_nNum;am.
rwi by_cases_if_not H8;au. rwi by_cases_if H8;au.
nin H9;subst. ap oS_nNum;am.
rwi by_cases_if_not H8;au. rwi by_cases_if_not H8;au.
uhg;ir.
assert (inc emptyset (card x)).
rw ordinal_inc_not_sub. uhg;ir.
destruct emptyset_empty with emptyset. ap H7.
ap H0. ap emptyset_N.
ap emptyset_ordinal. ap card_ordinal.
apply H6 in H7. nin H7;ee.
rwi create_ev H8;au.
apply by_cases with (inc x0 nNum);ir.
rwi by_cases_if H8;au.
destruct emptyset_empty with x0. wr H8. rw oS_inc. au.
rwi by_cases_if_not H8;au.
subst. ap H9. ap emptyset_N.

destruct H6 as [g H6].
ee.
pose (h := compose (inverse f) (compose g (f))).
exists h;ee.
uf h. eapply injective_compose. eapply injective_compose.
ap bijective_injective. am. am. ap bijective_injective;am.
uhg;ir.
assert (g = compose f (compose h (inverse f))).
uf h.
cp compose_axioms.
 rw compose_assoc;try am.
rw compose_assoc;try am. rw H4.
wr compose_assoc;au. wr compose_assoc;au. rw H4.
erewrite map_compose_id_r. erewrite map_compose_id_l.
tv. am. am.
ap id_axioms.
ap H7. rw H9. eapply bijective_compose.
eapply bijective_compose. am. am. am.
Qed.

Lemma inj_bij_finite : forall x, (forall f, injective x x f -> bijective x x f) -> 
is_finite x.
Proof.
ir. ap excluded_middle;uhg;ir.
apply finite_inj_bij_contra in H0. nin H0;ee.
au.
Qed.

Lemma inj_bij_trans_finite : forall x, (forall f, Application.injective x x f ->
Application.bijective x x f) -> is_finite x.
Proof.
ir. ap inj_bij_finite. ir.
cp (injective_of_map H0). apply H in H1.
uhg;ee;au.
Qed.

Lemma finite_rw : is_finite = (fun x => forall f, injective x x f -> bijective x x f).
Proof.
ap arrow_extensionality;ir.
ap iff_eq. ap finite_inj_bij.
ap inj_bij_finite.
Qed.

Lemma finite_trans_rw : is_finite = (fun x => 
forall f, Application.injective x x f -> Application.bijective x x f).
Proof.
ap arrow_extensionality;ir.
ap iff_eq. ap finite_inj_bij_trans.
ap inj_bij_trans_finite.
Qed.

Lemma nNum_iso_sub_sub : forall x, inc x nNum -> forall y, inc y nNum -> 
iso_sub x y -> sub x y.
Proof.
ir. wr (nNum_card H). wr (nNum_card H0).
ap iso_sub_card_sub. am.
Qed.

Definition is_infinite x := ~is_finite x.

Lemma infinite_omega_sub_card : is_infinite = (fun x => sub nNum (card x)).
Proof.
ap arrow_extensionality;intros x.
ap iff_eq;ir.
rw ordinal_sub_not_inc;au.
uhg;ir;ap H. ap card_nNum_finite. am.
ap omega_ordinal. ap card_ordinal.
uhg;uhg;ir.
apply finite_card_nNum in H0.
apply H in H0.
apply ordinal_not_inc_self with (card x).
ap card_ordinal. am.
Qed.

Lemma finite_sub : forall x, is_finite x -> forall y, sub y x -> is_finite y.
Proof.
ir. apply finite_card_nNum in H.
assert (sub (card y) (card x)).
ap sub_card_sub.
am.
ap card_nNum_finite.
ap (ordinal_sub_inc_trans (card_ordinal y) H1 omega_ordinal H).
Qed.

Lemma finite_iso_sub : forall x, is_finite x -> forall y, iso_sub y x -> is_finite y.
Proof.
ir. nin H0.
ee. eapply finite_invariant. eapply finite_sub. am. am. ap are_equipotent_sym;am.
Qed.

Lemma singleton_finite : forall x, is_finite (singleton x).
Proof.
ir. ap inj_bij_trans_finite. ir.
uhg;ee;try am. uhg;ir.
cp H0. apply H in H0. apply singleton_eq in H0;apply singleton_eq in H1.
exists x;ee. ap singleton_inc. rw H1. rwi H1 H0. am.
Qed.

Lemma Im_finite : forall x, is_finite x -> forall f, is_finite (Im f x).
Proof.
ir. eapply finite_iso_sub. am.
ap Im_iso_sub.
Qed.

Lemma card_emptyset : card emptyset = emptyset.
Proof.
ap nNum_card. ap emptyset_N.
Qed.

Lemma card_finite_tack_on : forall a, is_finite a -> forall x, ~ inc x a -> 
card (tack_on a x) = oS (card a).
Proof.
ir.
assert (is_finite (tack_on a x)). constructor. am.
cp (finite_card_nNum H). cp (finite_card_nNum H1).
transitivity (card (oS (card a))).
Focus 2. ap nNum_card. ap oS_nNum. am.
ap card_invariant.
cp (card_equipotent a).
ap trans_equipotent.
rwi are_equipotent_transformation H4.
destruct H4 as [f H4].
exists (fun n => by_cases 
(fun _ : n=x => card a)
(fun _ : _ => f n)).
uhg;ee;uhg;ir.
rwi tack_on_inc H5;nin H5.
rw by_cases_if_not. rw oS_inc;left.
ap H4. am.
uhg;ir;subst;au.
subst. rw by_cases_if. rw oS_inc;au. tv.
rwi tack_on_inc H5;rwi tack_on_inc H6;nin H5;nin H6;subst.
rwi by_cases_if_not H7. rwi by_cases_if_not H7. ap H4;am.
uhg;ir;subst;au. uhg;ir;subst;au.
rwi by_cases_if_not H7. rwi by_cases_if H7;tv.
assert (inc (f x0) (card a)). ap H4. am.
rwi H7 H6. apply ordinal_not_inc_self in H6. nin H6.
ap card_ordinal.
uhg;ir;subst;au.
rwi by_cases_if H7. rwi by_cases_if_not H7.
assert (inc (f y) (card a)). ap H4. am.
wri H7 H5. apply ordinal_not_inc_self in H5. nin H5.
ap card_ordinal.
uhg;ir;subst;au.
tv.
tv.
rwi oS_inc H5;nin H5.
apply H4 in H5. nin H5;ee;subst.
exists x0;ee. rw tack_on_inc;au.
rw by_cases_if_not. tv. uhg;ir;subst;au.
subst. exists x. ee.
rw tack_on_inc;au.
rw by_cases_if;tv.
Qed.

Lemma finite_surj_bij_trans : forall x, is_finite x -> 
forall f, Application.surjective x x f -> Application.bijective x x f.
Proof.
ir.
pose (g y := choose (fun z => inc z x & f z = y)).
assert (forall y, inc y x -> (inc (g y) x & f (g y) = y)).
ir. uf g. ap choose_pr. apply H0 in H1. nin H1. exists x0;am.
assert (Application.injective x x g).
uhg;ee;uhg;ir.
ap H1. am.
cp (uneq f H4).
cp (H1 x0 H2);cp (H1 y H3).
ee. rwi H9 H5. rwi H8 H5. am.
apply (finite_inj_bij_trans H) in H2.
apply inverseT_bijective with g.
am. am.
uhg;ee;ir.
cp H3. apply H2 in H4. nin H4;ee;subst.
cp (H1 x1 H4). ee. rw H6.
tv.
ap H1;am.
Qed.

End Finite.


