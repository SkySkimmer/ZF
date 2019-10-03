
Set Implicit Arguments.
Unset Strict Implicit.

Require Export functions.
Require Export ordinals.

Module Lci.

Section Law.

Variable (law : E2).

Definition is_lci a := (forall x, inc x a -> forall y, inc y a -> inc (law x y) a).

Definition associative a := forall x, inc x a -> forall y, inc y a -> forall z, inc z a -> 
law x (law y z) = law (law x y) z.

Definition commutative a := forall x, inc x a -> forall y, inc y a -> 
law x y = law y x.

Definition is_neutre a e := 
A (inc e a)
(A (forall x, inc x a -> law x e = x)
(forall x, inc x a -> law e x = x)).

Lemma neutre_unicity : forall a, unicity (is_neutre a).
Proof.
ir;uhg;intros e H e';ir. uh H;uh H0;ee.
rewrite <- H2 with e'. rewrite H3. tv.
am. am.
Qed.

Definition are_inverse a e x y := 
A (inc x a)
(A (inc y a)
(A (law x y = e)
(law y x = e))).

Definition inversible a e x := exists y, (are_inverse a e x y).

Definition inverse_of a e x := unique_choose (are_inverse a e x).

Definition unifere a := ex (is_neutre a).

Definition is_monoid a e := 
A (is_lci a)
(A (is_neutre a e)
(associative a)).

Lemma inverse_unicity : forall a e, is_monoid a e ->
forall x, (unicity (are_inverse a e x)).
Proof.
uhg;ir. uh H;uh H0;uh H1;ee. uh H4;uh H9;ee.
wr H10. wr H7. rw H9. rw H6. rw H11. tv.
am. am. am. am. am.
Qed.

Definition is_group a e :=
A (is_lci a)
(A (is_neutre a e)
(A (associative a)
(forall x, inc x a -> inversible a e x))).

Lemma group_rw : forall a e, is_group a e = A (is_monoid a e) (forall x, inc x a -> inversible a e x).
Proof.
ir. ap iff_eq;ir.
uh H;ee. uhg;ee;am. am.
ee. uh H;uhg;ee;am.
Qed.

Lemma group_is_monoid : forall a e, is_group a e -> is_monoid a e.
Proof.
ir. uh H;uhg;ee;am.
Qed.

Definition is_abelian_group a e := 
A (is_group a e)
(commutative a).

Definition is_reg_l a := (forall x, inc x a -> forall y, inc y a -> forall y', inc y' a -> 
law x y = law x y' -> y=y').

Definition is_reg_r a := (forall x, inc x a -> forall y, inc y a -> forall y', inc y' a -> 
law y x = law y' x -> y=y'). 

Definition is_regular a := A (is_reg_l a) (is_reg_r a).

Lemma group_is_regular : forall a e, is_group a e -> is_regular a.
Proof.
ir. uh H;ee. uh H0;ee. uh H1;ee.
uhg;ee;uhg;ir.
wr H4. symmetry. wr H4.
destruct H2 with x. am.
ee.
uh H9;ee.
wr H12. wr H1;au. wr H1;au.
rw H8. tv. am. am.
wr H3;au. symmetry;wr H3;au.
destruct H2 with x. am.
ee. uh H9;ee.
wr H11. rw H1. rw H1. rw H8. tv.
am. am. am. am. am. am. 
Qed.

Lemma inversible_inverse_of : forall a e, is_monoid a e -> 
forall x, inversible a e x -> 
are_inverse a e x (inverse_of a e x).
Proof.
ir. uh H0;ee. uf inverse_of. ap unique_choose_pr.
nin H0. ee. exists x0. am.
ir. eapply inverse_unicity. am.
Qed.

Lemma inverse_of_eq :  forall a e, is_monoid a e ->
forall x y, are_inverse a e x y -> 
y = inverse_of a e x.
Proof.
ir. eapply inverse_unicity;try am.
ap inversible_inverse_of. am. exists y;am.
Qed.

Lemma group_inverse_of : forall a e, is_group a e -> forall x, inc x a -> 
are_inverse a e x (inverse_of a e x).
Proof.
ir. ap inversible_inverse_of. ap group_is_monoid;am. uh H;ee. ap H3. am.
Qed.

Lemma are_inverse_symm : forall a e x y, are_inverse a e x y -> are_inverse a e y x.
Proof.
ir. uhg;ee;am.
Qed.

Lemma inverse_inverse_rw : forall a e, is_group a e -> forall x y, are_inverse a e x y ->
forall y', are_inverse a e y y' -> x=y'.
Proof.
ir. uh H0;uh H1;ee. uh H;ee. uh H8;ee.
wr H11. wr H7. uh H9;ee. rw H9. rw H5. rw H12.
tv. am. am. am. am. am.
Qed.

Lemma inversible_inverse_inc : forall a e, is_monoid a e -> 
forall x, inversible a e x -> inc (inverse_of a e x) a.
Proof.
ir. apply inversible_inverse_of in H0. uh H;ee. am. am.
Qed.

Lemma group_inverse_inc : forall a e, is_group a e -> forall x, inc x a -> 
inc (inverse_of a e x) a.
Proof.
ir. ap inversible_inverse_inc. uh H;ee.
uhg;ee;am. ap H;am.
Qed.

Lemma inverse_inverse : forall a e, is_group a e -> forall x, inc x a -> 
x = inverse_of a e (inverse_of a e x).
Proof.
ir. apply inverse_inverse_rw with a e (inverse_of a e x). am.
ap group_inverse_of. am. am. ap group_inverse_of. am.
ap group_inverse_inc. am. am.
Qed.

Lemma are_inverse_rw : forall a e, is_group a e -> forall x, inc x a ->
forall y, are_inverse a e x y = (y = inverse_of a e x).
Proof.
ir. ap iff_eq;ir.
eapply inverse_unicity.
ap group_is_monoid. ap H.
ap H1. ap group_inverse_of. am. am.
rw H1;ap group_inverse_of. am. am.
Qed.

Lemma inverse_of_neutre : forall g e, is_monoid g e -> inverse_of g e e = e.
Proof.
ir.
assert (are_inverse g e e e).
uhg;ee. am. am. uh H;ee. uh H0;ee.
ap H3. am. uh H;ee;uh H0;ee;ap H3. am.
apply inverse_unicity with g e e. am.
ap inversible_inverse_of. am. exists e;am. am.
Qed.


Lemma inverse_injective : forall g e, is_group g e -> 
forall x y, inc x g -> inc y g -> 
inverse_of g e x = inverse_of g e y -> 
x=y.
Proof.
ir. assert (is_regular g). eapply group_is_regular. am.
uh H3;ee.
assert (are_inverse g e x (inverse_of g e x)).
ap group_inverse_of. am. am.
assert (are_inverse g e y (inverse_of g e y)).
ap group_inverse_of;am.
uh H5;ee;uh H6;ee.
apply H3 with (inverse_of g e x). am. am.
am.
rw H9. rw H2. rw H12. tv.
Qed.

Lemma inverse_of_law : forall g e, is_monoid g e -> forall x y, inc x g -> inc y g -> 
inversible g e x -> inversible g e y -> 
inverse_of g e (law x y) = law (inverse_of g e y) (inverse_of g e x).
Proof.
ir.
assert (are_inverse g e (law x y) (law (inverse_of g e y) (inverse_of g e x))).
uhg;ee. ap H;am. ap H ;ap inversible_inverse_inc;am.
cp (inversible_inverse_of H H2); cp (inversible_inverse_of H H3).
uh H;ee. rw H7;au. replace (law (law x y) (inverse_of g e y)) with
(law x e). uh H6;ee. rw H8;au. wr H7;au. uh H5;ee. rw H9. tv.
uh H;ee. apply inversible_inverse_of in H2. apply inversible_inverse_of in H3.
rw H5;au. replace (law (law (inverse_of g e y) (inverse_of g e x)) x) with
(law (inverse_of g e y) e). uh H4;ee. rw H6;au.
symmetry. wr H5;au. uh H2;ee. rw H8;tv.
ap H;au. uhg;ee;am. uhg;ee;am.
eapply inverse_unicity. ap H. ap inversible_inverse_of. am. uhg.
exists (law (inverse_of g e y) (inverse_of g e x)). am.
am.
Qed.

Lemma group_inverse_of_law : forall g e, is_group g e -> forall x y, inc x g -> inc y g -> 
inverse_of g e (law x y) = law (inverse_of g e y) (inverse_of g e x).
Proof.
ir. ap inverse_of_law. ap group_is_monoid;am.
am. am. ap H;am. ap H;am.
Qed.

Section Subgroups.

Variables (a e : E).

Hypothesis hyp : is_group a e.

Definition is_subgroup b := 
A (sub b a)
(is_group b e).

Lemma subgroup_show_fast : forall b, sub b a -> 
inc e b -> 
(forall x y, inc x b -> inc y b -> inc (law x (inverse_of a e y)) b) -> 
is_subgroup b.
Proof.
ir.
uhg;ee.
am.

assert (Hax : is_lci b).
uhg;ir.
replace y with (inverse_of a e (inverse_of a e y)).
ap H1. am.
cp hyp. uh H4;nin H4. nin H5. nin H6.
set (y' := (inverse_of a e y)).
replace y' with (law e y'). uf y'.
ap H1. am. am. uh H5;nin H5. nin H8. ap H9. uf y'.
ap group_inverse_inc. uhg. split. am. split. am. am. au.
wr inverse_inverse. tv. am. au.

uhg;ee. am.

uhg. ee. am.
ir. cp hyp. uh H3;ee. uh H4;ee.
ap H7;au.
ir. cp hyp;uh H3;ee. uh H4;ee.
ap H8;au.

cp hyp. uh H2;ee.
uhg;ir.
ap H4;au.

ir. exists (inverse_of a e x). assert (inc (inverse_of a e x) b).
set (y' := (inverse_of a e x)).
replace y' with (law e y'). uf y'.
ap H1. am. am. cp hyp. uh H3;ee. uh H4;ee. ap H8. uf y'.
ap group_inverse_inc. am. au.

uhg;ee. am.
am.
assert (are_inverse a e x (inverse_of a e x)).
ap group_inverse_of. am. au.
uh H4;ee. ap H6. 
assert (are_inverse a e x (inverse_of a e x)).
ap group_inverse_of;au. uh H4;ee.
ap H7.
Qed.

Lemma subgroup_show : forall b, sub b a -> 
(exists e', inc e' b) -> 
(forall x y, inc x b -> inc y b -> inc (law x y) b) -> 
(forall x, inc x b -> inc (inverse_of a e x) b) -> 
is_subgroup b.
Proof.
ir. ap subgroup_show_fast.
am.

nin H0. cp H0. apply H2 in H3.
apply group_inverse_of with a e x in hyp. nin hyp;ee.
wr H6. ap H1. am. am.
au.
ir. ap H1. am. ap H2. am.
Qed.

Lemma subgroup_inverse_eq : forall b, is_subgroup b -> forall x, inc x b -> 
inverse_of a e x = inverse_of b e x.
Proof.
ir. assert (are_inverse a e x (inverse_of a e x)).
ap group_inverse_of. am. uh H;ee. ap H;am.
apply inverse_unicity with a e x.
ap group_is_monoid;am. am.
assert (inc (inverse_of b e x) b).
ap group_inverse_inc. am. am.
assert (are_inverse b e x (inverse_of b e x)).
ap group_inverse_of. am. am.
uhg;ee. uh H;ee. ap H;am.
uh H;ee;ap H;am.
uh H;ee. uh H;ee. au. au.
Qed.

Lemma subgroup_inter : forall Eb, nonempty Eb -> (forall b, inc b Eb -> is_subgroup b) -> 
is_subgroup (inter Eb).
Proof.
ir. nin H. ap subgroup_show.
uhg;ir.
cp (inter_all H1 H).
apply H0 in H. uh H;ee. au.

exists e. ap inter_inc. econstructor. ap H.
ir. apply H0 in H1;uh H1;ee.
uh H2;ee. uh H3;ee.
am.
ir. ap inter_inc. econstructor;ap H.
ir. cp H3. apply H0 in H3;uh H3;ee.
uh H5;ee. uh H5;ee. apply H5.
cp (inter_all H1 H4). am.
eapply inter_all. am. am.

ir.
ap inter_inc. econstructor;ap H.
ir. cp H2. apply H0 in H3. uh H3;ee. uh H4;ee.
destruct H7 with x0. cp (inter_all H1 H2). am.
uh H8;ee.
assert (inverse_of a e x0 = x1).
apply inverse_unicity with a e x0.
ap group_is_monoid;am.
ap group_inverse_of. am. ap H3. eapply inter_all;am.
uhg;ee. au. au. am. am.
rw H12. am.
Qed.

Lemma neutre_is_subgroup : is_subgroup (singleton e).
Proof.
ap subgroup_show.
uhg;ir. apply singleton_eq in H;rw H. am.
exists e;ap singleton_inc.
ir. apply singleton_eq in H;apply singleton_eq in H0;rw H;rw H0. nin hyp;ee. uh H2;ee.
rw H5;au. ap singleton_inc.
ir. apply singleton_eq in H;rw H.
cp hyp. rw inverse_of_neutre;au. ap singleton_inc.
ap group_is_monoid;am.
Qed.

Lemma group_is_subgroup : is_subgroup a.
Proof.
uhg. ee. uhg;ir;am.
am.
Qed.

End Subgroups.

Lemma group_show_by_subgroup : forall g e, (exists h, is_subgroup h e g) -> 
is_group g e.
Proof.
ir. nin H. uh H. ee. am.
Qed.

End Law.


Module Morphisms.
Export Function. Export Map.

Section LawSec.

Variables (law : E2) (g : E) (law' : E2) (g' : E).

Definition morphismT (f:E1) := (forall x y, inc x g -> inc y g -> 
f (law x y) = law' (f x) (f y)).

Definition is_morphism f := 
A (is_map g g' f) (morphismT (ev f)).

Lemma trans_of_morphism : forall f, is_morphism f -> 
Application.axioms g g' (ev f).
Proof.
ir. ap trans_of_map. am.
Qed.

Definition is_isomorphism f :=
A (bijective g g' f)
(morphismT (ev f)).

Lemma isomorphism_morphism : forall f, is_isomorphism f -> is_morphism f.
Proof.
ir;uhg;ee;am.
Qed.

Lemma morphism_reg_neutre : forall e e', is_neutre law g e -> is_neutre law' g' e' -> is_regular law' g' -> 
forall f, is_morphism f -> ev f e = e'.
Proof.
ir. uh H1;ee.
apply H1 with (ev f e).
ap (trans_of_map (and_P H2));am. ap (trans_of_map (and_P H2));am. 
ap H0.
uh H2;ee. wr H4.
uh H;uh H0;ee.
rw H6;try am.
symmetry. ap H5;au.
ap (trans_of_map H2). am.
am. am.
Qed.

Lemma morphism_neutre : forall e e', is_group law g e -> is_group law' g' e' -> forall f,
is_morphism f -> ev f e = e'.
Proof.
intros e e' H H0.
ap morphism_reg_neutre. am. am. ap (group_is_regular H0).
Qed.

Lemma morphism_inversible_inverse : forall e e', is_monoid law g e -> is_monoid law' g' e' -> 
forall Hreg : is_regular law' g',
forall f, is_morphism f -> 
forall x, inversible law g e x -> 
ev f (inverse_of law g e x) = inverse_of law' g' e' (ev f x).
Proof.
ir. ap inverse_of_eq. am.
nin H2. cp H2. apply inverse_of_eq in H2;try am.
subst. uhg;ee.
eapply trans_of_map. am. am.
eapply trans_of_map. am. am.
uh H3;ee.
uh H1;ee. wr H6;au.
rw H4. ap morphism_reg_neutre. am. am. am.
uhg;ee;am. uh H3;ee;uh H1;ee.
wr H6;au. rw H5.  
 ap morphism_reg_neutre. am. am. am. uhg;ee;am.
Qed.

Lemma morphism_inverse : forall e e', is_group law g e -> is_group law' g' e' -> 
forall f, is_morphism f -> forall x, inc x g -> 
ev f (inverse_of law g e x) = inverse_of law' g' e' (ev f x).
Proof.
ir.
ap morphism_inversible_inverse;try ap group_is_monoid;try am.
eapply  group_is_regular. am.
ap H;am.
Qed.

Definition Ker g e' (f : E1) := (Z g (fun x => f x = e')).

Lemma Ker_sub_group : forall e e', is_group law g e -> is_group law' g' e' -> 
forall f, is_morphism f ->
is_subgroup law g e (Ker g e' (ev f)).
Proof.
ir. ap subgroup_show.
am.
uhg;ir. ufi Ker H2;Ztac; au.
exists e. ap Z_inc. am.
apply morphism_neutre. am. am. uhg;ee;am.
ir. ufi Ker H2;Ztac;au;ufi Ker H3;Ztac;au.
uh H1;ee.
ap Z_inc. uh H;ee. ap H. am. am.
rw H6. rw H5;rw H4.
uh H0;ee. uh H9;ee. ap H7. ap H7. am.
am.

ir. uh H1;ee. cp H;cp H0.
uh H4;ee. uh H5;ee.
ap Z_inc. ap group_inverse_inc. am.
ufi Ker H2;Ztac;au.
rewrite morphism_inverse with e e' f x.
ufi Ker H2;Ztac;au.
rw H12. ap inverse_of_neutre. ap group_is_monoid;am. am. am. uhg;ee;am.
ufi Ker H2;Ztac;au.
Qed.

Lemma Ker_injective : forall e e', is_group law g e -> is_group law' g' e' -> 
forall f, is_morphism f -> Ker g e' (ev f) = singleton e -> injective g g' f.
Proof.
ir. uhg;ee. am.
uhg;ir.
apply inverse_injective with law g e. am. am. am.
assert (is_regular law g). apply group_is_regular with e. am.
uh H6;ee. uh H1;ee.
apply H6 with y. am. ap group_inverse_inc. am.
am. ap group_inverse_inc. am. am.
assert (Lci.are_inverse law g e y (inverse_of law g e y)).
 ap group_inverse_of. am. am.
uh H9;ee. rw H11.
assert (inc (law y (inverse_of law g e x)) (Ker g e' (ev f))).
ap Z_inc. uh H;ee. ap H.
am. ap group_inverse_inc. uhg;ee;am. am.
rw H8. rewrite morphism_inverse with e e' f x.
rw H5. assert (Lci.are_inverse law' g' e' (ev f y) (inverse_of law' g' e' (ev f y))).
ap group_inverse_of. am. ap (trans_of_map H1);am.
uh H13;ee. am. am. am. uhg;ee;am. am. am.
ap group_inverse_inc. am. am.
rwi H2 H13. apply singleton_eq in H13. am.
Qed. 
(* note : hypotheses (maybe) cannot be reduced 
as we need every elmt to be inversible *)

Lemma injective_reg_Ker : forall e e', is_neutre law g e -> is_neutre law' g' e' -> 
is_regular law' g' -> 
forall f, is_morphism f -> injective g g' f -> 
Ker g e' (ev f) = singleton e.
Proof.
ir. ap extensionality;uhg;ir.
ufi Ker H4;apply Z_all in H4;ee.
replace a with e. ap singleton_inc.
ap H3.
am. am.
rw H5. eapply morphism_reg_neutre.
ap H. am. am. am.
apply singleton_eq in H4;subst.
ap Z_inc. am.
eapply morphism_reg_neutre;am.
Qed.

Lemma injective_Ker : forall e e', is_group law g e -> is_group law' g' e' -> 
forall f, is_morphism f -> injective g g' f -> 
Ker g e' (ev f) = singleton e.
Proof.
intros e e' H H0.
ap injective_reg_Ker.
am. am. ap (group_is_regular H0).
Qed.

Lemma neutre_in_Ker : forall e e', is_neutre law g e -> is_neutre law' g' e' -> 
is_regular law' g' -> 
forall f, is_morphism f -> 
inc e (Ker g e' (ev f)).
Proof.
ir. ap Z_inc. am.
rewrite morphism_reg_neutre with e e' f;au;am.
Qed.

Lemma injective_Ker_rw : forall e e', is_group law g e -> is_group law' g' e' -> 
forall f, is_morphism f -> 
injective g g' f = (Ker g e' (ev f) = singleton e).
Proof.
ir. ap iff_eq;ir.
eapply injective_Ker;au.
eapply Ker_injective. ap H. ap H0. am. am. 
Qed.

Lemma Im_sub_group : forall e e', is_group law g e -> is_group law' g' e' -> 
forall f, is_morphism f -> 
is_subgroup law' g' e' (Im (ev f) g).
Proof.
ir.
uh H1;ee.
ap subgroup_show. am.
uhg;ir. apply Im_ex in H3. nin H3. ee.
rw H4. ap (trans_of_map H1). am.

exists e'. ap Im_show_inc. exists e. ee. am. symmetry;eapply morphism_neutre.
ap H. am. uhg;ee;am. 

ir. apply Im_ex in H3;apply Im_ex in H4;nin H3;nin H4;ee.
rw H6;rw H5. wr H2;au. ap Im_inc. uh H;ee;ap H;au.

ir. apply Im_ex in H3;nin H3;ee.
rw H4. rewrite <-morphism_inverse with e e' f x0;au.
ap Im_inc. ap group_inverse_inc;au. uhg;ee;am.
Qed.

Lemma isomorphism_inverse_are_inverse : forall f, is_isomorphism f ->
are_inverse g g' f (inverse f).
Proof.
ir. ap bijective_inverse_of. am.
Qed.


Lemma const_neutre_is_morphism : is_lci law g -> forall e', is_neutre law' g' e' -> 
is_morphism (L g (fun x:E => e')).
Proof.
ir. uhg;ee. ap map_of_trans. uhg;ir. am.
uhg;ir. rw create_ev. rw create_ev. rw create_ev. uh H0;ee. rw H3;au.
am. am. ap H;am.
Qed.


Definition morphism_set := Z (map_set g g') is_morphism.

Lemma morphism_morphism_set : forall f, is_morphism f -> 
inc f morphism_set.
Proof.
ir;ap Z_inc. ap map_map_set.
am. am.
Qed.

End LawSec.


Lemma isomorphism_inverse_isomorphism : forall law g law' g', 
is_lci law g -> is_lci law' g' -> 
forall f, is_isomorphism law g law' g' f -> 
is_isomorphism law' g' law g (inverse f).
Proof.
ir. cp (isomorphism_inverse_are_inverse H1).
uhg;ee. eapply are_inverse_bijective. ap are_inverse_sym. am. 
uhg;ir. set (f' := inverse f).
replace (ev f' (law' x y) = law (ev f' x) (ev f' y)) with
(ev f' (law' (ev f (ev f' x)) (ev f (ev f' y))) = law (ev f' x) (ev f' y)).
uh H1;ee.
wr H5;au. uh H2;ee. fold f' in H7.
uh H7;ee. rw H7. tv.
ap H. eapply trans_of_map;am.
eapply trans_of_map;am. eapply trans_of_map;am.
eapply trans_of_map;am.

uh H2;ee. uh H6;ee. 
cp (trans_of_map H2). cp (trans_of_map H5).
rw H7;au. rw H7;au.
Qed.

Definition is_endomorphism law g f := is_morphism law g law g f.

Definition endomorphism_set law g := Z (map_set g g) (is_endomorphism law g).

Lemma morphism_compose : 
forall law g (H : is_lci law g),
forall law' g',
forall f, is_morphism law g law' g' f ->
forall law'' g'',
forall f', is_morphism law' g' law'' g'' f' -> 
is_morphism law g law'' g'' (compose f' f).
Proof.
intros law g H law' g' f H1 law'' g'' f' H3;uhg;ee.
eapply map_compose;am.
uhg;ir.
erewrite map_compose_ev. Focus 2. am. Focus 2.
am.
Focus 2. ap H. am. am.
erewrite compose_ev;try am.
erewrite compose_ev;try am.
etransitivity. Focus 2.
ap H3. eapply trans_of_map;am. eapply trans_of_map;am.
ap uneq. ap H1;au.
eapply eq_ind. am.
symmetry. eapply map_compose.
am. am.
eapply eq_ind. am.
symmetry. eapply map_compose.
am. am.
Qed.

Lemma endomorphism_compose : forall law g, is_lci law g -> 
forall f f', is_endomorphism law g f -> is_endomorphism law g f' -> 
is_endomorphism law g (compose f' f).
Proof.
ir. uhg. eapply morphism_compose. am. am. am.
Qed.

Definition is_automorphism law g f := is_isomorphism law g law g f.

Lemma isomorphism_compose : 
forall law g (H : is_lci law g),
forall law' g',
forall f, is_isomorphism law g law' g' f ->
forall law'' g'',
forall f', is_isomorphism law' g' law'' g'' f' -> 
is_isomorphism law g law'' g'' (compose f' f).
Proof.
ir;uhg;ee.
eapply bijective_compose. am. am.
eapply morphism_compose. am. uhg;ee;am.
uhg;ee;am.
Qed.

Lemma automorphism_compose : forall law g, is_lci law g -> 
forall f f', is_automorphism law g f -> is_automorphism law g f' -> 
is_automorphism law g (compose f' f).
Proof.
ir. uhg. eapply isomorphism_compose. am. am. am.
Qed.

Lemma endomorphism_compose_monoid : forall law g, is_lci law g -> 
is_monoid compose (endomorphism_set law g) (id g).
Proof.
ir;uhg;ee.
uhg. ir.
apply Z_pr in H0;apply Z_pr in H1.
ap morphism_morphism_set. ap endomorphism_compose.
am. am. am.
uhg;ee;ir.
ap morphism_morphism_set.
uhg;ee. ap id_map. uhg;ir.
repeat rw id_ev;au.
eapply map_compose_id_r. apply Z_pr in H0.
am.
eapply map_compose_id_l. apply Z_pr in H0.
am.
uhg;ir.
apply Z_pr in H0;apply Z_pr in H1;apply Z_pr in H2.
eapply map_compose_assoc;am.
Qed.

Lemma id_automorphism : forall law g, is_lci law g -> is_automorphism law g (id g).
Proof.
ir;uhg;uhg;ee. ap id_bijective.
uhg;ir. repeat rw id_ev;au. 
Qed.

Definition automorphism_set law g := Z (endomorphism_set law g) (bijective g g).

Lemma automorphism_set_rw : forall law g f, inc f (automorphism_set law g) = is_automorphism law g f.
Proof.
ir;ap iff_eq;ir.
apply Z_all in H. ee. apply Z_pr in H. uhg;uhg;ee;am.
ap Z_inc. ap morphism_morphism_set. uhg;ee;am.
am.
Qed.

Lemma automorphism_compose_group : forall law g, is_lci law g -> 
is_group compose (automorphism_set law g) (id g).
Proof.
ir.
uhg;ee. uhg;ir.
rwi automorphism_set_rw H0;rwi automorphism_set_rw H1;rw automorphism_set_rw.
ap automorphism_compose;am.
uhg;ee;ir. rw automorphism_set_rw. ap id_automorphism. am.
ap (and_P (and_Q (endomorphism_compose_monoid H))).
rwi automorphism_set_rw H0;ap morphism_morphism_set. uhg;ee;am.
ap (and_P (and_Q (endomorphism_compose_monoid H))).
rwi automorphism_set_rw H0;ap morphism_morphism_set. uhg;ee;am.
uhg;ir.
ap (and_Q (and_Q (endomorphism_compose_monoid H)));eapply Z_sub;am.

ir. rwi automorphism_set_rw H0.
cp (isomorphism_inverse_isomorphism H H H0).
econstructor;uhg;ee.
rw automorphism_set_rw. am.
rw automorphism_set_rw. am.
eapply bijective_inverse_compose_r. am.
eapply bijective_inverse_compose_l. am.
Qed.

End Morphisms.

Module Engender.
Import Ordinal.

Section Law.

Variables (law : E2) (g : E).

Inductive engenders (h : E) : EP := 
  | engenders_in : forall x, inc x h -> engenders h x
  | engenders_law : forall x, engenders h x -> forall y, engenders h y -> engenders h (law x y)
.

Definition is_engendered_set h x := forall y, inc y x <-> engenders h y.

Lemma engendered_set_unicity : forall h, unicity (is_engendered_set h).
Proof.
uhg;ir. ap extensionality;uhg;ir.
ap H0. ap H. am.
ap H;ap H0;am.
Qed.

Inductive engenders_lvl (h : E) : E -> EP :=
  | engenders_0 : forall x, inc x h -> engenders_lvl h emptyset x
  | engenders_S : forall n, inc n nNum -> forall x m, inc m n -> engenders_lvl h m x -> 
                    forall y m', inc m' n -> engenders_lvl h m' y -> engenders_lvl h n (law x y)
.

Lemma lvl_to_engenders : forall h n x, engenders_lvl h n x -> engenders h x.
Proof.
ir;nin H.
constructor. am.
ap engenders_law;am.
Qed.

Lemma lvl_to_nNum : forall h n x, engenders_lvl h n x -> inc n nNum.
Proof.
ir;nin H. ap emptyset_N. am.
Qed.

Lemma engenders_to_lvl : forall h x, engenders h x -> exists n, engenders_lvl h n x.
Proof.
ir;nin H. exists emptyset. constructor. am.

nin IHengenders1;nin IHengenders2.
assert (exists z, inc x0 z & inc x1 z & inc z nNum).
cp (lvl_to_nNum H1);cp (lvl_to_nNum H2).
cp (nNum_ordinal H3);cp (nNum_ordinal H4).
destruct ordinal_sub_sub with x0 x1;try am.
exists (oS x1);ee. rw oS_inc. rwi ordinal_sub_leq_of H7;au.
rw oS_inc;au. ap oS_nNum;am.
exists (oS x0);ee. rw oS_inc;au. rw oS_inc. rwi ordinal_sub_leq_of H7;au.
ap oS_nNum;am.
nin H3;ee.
exists x2. apply engenders_S with x0 x1;am.
Qed.

Lemma engendered_set_ex : forall h, ex (is_engendered_set h).
Proof.
ir.
pose (is_eng_lvl := fun n x => forall y, inc y x <-> engenders_lvl h n y).
assert (forall n, unicity (is_eng_lvl n)). uhg;ir.
ap extensionality;uhg;ir.
ap H0. ap H. am. ap H;ap H0;am.
assert (forall n, inc n nNum -> ex (is_eng_lvl n)).
ap nNum_wo_ind.
ir.
set (f := fun a => unique_choose (is_eng_lvl a)).
assert (forall a, inc a n -> is_eng_lvl a (f a)).
uf f;ir. ap unique_choose_pr. ap H1;am. ap H.

apply nNum_destruct in H0. nin H0. subst.
exists h. uhg;split;ir. constructor. am.
inversion H0;subst. am. edestruct emptyset_empty;am.
destruct H0 as [m  H0];ee;subst.
assert (forall x, engenders_lvl h (oS m) x -> (exists y, exists z, exists a, exists b, 
inc a (oS m) & inc b (oS m) & engenders_lvl h a z & engenders_lvl h b y & x = law z y)).
ir. inversion H3;subst.
destruct emptyset_empty with m. rw H4. rw oS_inc;au.
econstructor;econstructor;econstructor;econstructor.
ee. Focus 5. reflexivity.
Focus 3. am. am. Focus 2. am. am.
pose (X := union (Im2 (fun a b => Im2 law (f a) (f b)) (oS m) (oS m))).
exists X. uhg;split;ir.
union_nin H4.
apply Im2_ex in H4. nin H4;nin H4;ee;subst.
apply Im2_ex in H5. nin H5;nin H5;ee;subst.
apply H2 in H5;au. apply H2 in H7;au.
apply engenders_S with x0 x1. ap oS_nNum;am. am. am. am. am.

apply H3 in H4. nin H4;nin H4;nin H4;nin H4;ee;subst.
ap union_inc. econstructor. ee. ap Im2_inc. ap H4. ap H5. ap Im2_inc.
ap H2. am. am. ap H2;am.

set (f := fun a => unique_choose (is_eng_lvl a)).
assert (forall a, inc a nNum -> is_eng_lvl a (f a)).
uf f;ir. ap unique_choose_pr. ap H0. am. ap H.

pose (X := union (Im (fun n => f n) nNum)).
exists X. uhg;split;ir.
union_nin H2. Im_nin H2. subst.
apply H1 in H3;au. eapply lvl_to_engenders. am.
apply engenders_to_lvl in H2. nin H2.
ap union_inc. econstructor;ee. ap Im_inc. eapply lvl_to_nNum. am.
ap H1. eapply lvl_to_nNum. am. am.
Qed.

Definition engendered_set h := unique_choose (is_engendered_set h).

Lemma engendered_set_pr : forall h, is_engendered_set h (engendered_set h).
Proof.
ir;uf engendered_set;ap unique_choose_pr.
ap engendered_set_ex. uhg;ir;ap extensionality;uhg;ir.
ap H0;ap H;am. ap H;ap H0;am.
Qed.

Lemma engenders_sub_pr : forall h h', sub h h' -> forall x, engenders h x -> engenders h' x.
Proof.
ir;nin H0.
constructor;au.
ap engenders_law. am. am.
Qed.

Lemma engenders_sub : forall h h', sub h h' -> sub (engendered_set h) (engendered_set h').
Proof.
ir. uhg;ir. ap engendered_set_pr. eapply engenders_sub_pr. am.
ap engendered_set_pr. am.
Qed.

Lemma engenders_lci_inc : is_lci law g -> forall h, sub h g -> forall x, engenders h x -> inc x g.
Proof.
ir. nin H1. au.
ap H. am. am.
Qed.

Lemma engenders_lci_sub : is_lci law g -> forall h, sub h g -> sub (engendered_set h) g.
Proof.
ir;uhg;ir. eapply engenders_lci_inc. am. am. ap engendered_set_pr. am.
Qed.

Lemma engendered_set_lci : forall h, is_lci law (engendered_set h).
Proof.
ir;uhg;ir.
ap engendered_set_pr. ap engenders_law;ap engendered_set_pr;am.
Qed.

Lemma engendered_sub_initial : forall h, sub h (engendered_set h).
Proof.
uhg;ir;ap engendered_set_pr;constructor;am.
Qed.

End Law.

End Engender.

Module Commutative.
Import Engender.

Section Law.

Variables (law : E2) (g : E).
Hypotheses (Hlci : is_lci law g) (Hassoc : associative law g).

Definition is_comm_subset h := A (sub h g) (commutative law h).

Lemma singleton_comm_subset : forall x, inc x g -> is_comm_subset (singleton x).
Proof.
ir;uhg;ee. uhg;ir. apply singleton_eq in H0;subst;am.
uhg;ir. apply singleton_eq in H0;apply singleton_eq in H1;subst;tv.
Qed.

Lemma comm_subset_sub : forall h h', sub h h' -> is_comm_subset h' -> is_comm_subset h.
Proof.
ir;uhg;ee. apply sub_trans with h';am.
uhg;ir. ap H0;au.
Qed.

Lemma engenders_comm : forall h, is_comm_subset h -> is_comm_subset (engendered_set law h).
Proof.
ir. cp (and_P H).
uhg;dj. ap engenders_lci_sub. am. am.

uhg. cp (engenders_lci_inc Hlci H0).

intros x Hx.
apply engendered_set_pr in Hx. nin Hx.
ir. apply engendered_set_pr in H4. nin H4.
ap H;am.

rw Hassoc;au. rw IHengenders1. wr Hassoc;au.
rw IHengenders2. ap Hassoc;au.

ir.
wr Hassoc;au. rw IHHx2;au. rw Hassoc;au.
rw IHHx1;au. wr Hassoc;au.
Qed.

Lemma doubleton_comm_subset : forall x, inc x g -> forall y, inc y g -> law x y = law y x -> 
is_comm_subset (doubleton x y). ir;uhg;ee.
Proof.
uhg;ir;apply doubleton_or in H2;nin H2;subst;am.
uhg;ir.
apply doubleton_or in H2;apply doubleton_or in H3;nin H2;nin H3;subst;au.
Qed.

Lemma comm_subset_tack_on_e : forall e, is_neutre law g e -> 
forall h, is_comm_subset h -> 
is_comm_subset (tack_on h e).
Proof.
ir;uhg;ee.
uhg;ir. rwi tack_on_inc H1;nin H1;subst;au. ap H0. am. ap H.
uhg;ir. rwi tack_on_inc H1;rwi tack_on_inc H2;nin H1;nin H2;subst;au.
ap H0;am.
transitivity x. ap H;ap H0;am. symmetry;ap H;ap H0;am.
transitivity y. ap H;ap H0;am. symmetry;ap H;ap H0;am.
Qed.

End Law.

End Commutative.

Module Pow.
Import Ordinal.

Section Law.

Variables (law : E2) (g e : E).

(*for a given law pl and a given n in nNum, pow law x n = law x (law x (...))*)
Definition pow (x:E) n := nNum_repeat (law x) n e.

Notation "x ^ n" := (pow x n).

Lemma pow_0 : forall x, pow x emptyset = e.
Proof.
ir;uf pow;rw nNum_repeat_0.
 tv.
Qed.

Lemma pow_S : forall x n, inc n nNum -> pow x (oS n) = law x (pow x n).
Proof.
ir;ap nNum_repeat_S. am.
Qed.

Hypothesis (Hmon : is_monoid law g e).

Lemma pow_inc : forall x, inc x g -> forall n, inc n nNum -> inc (pow x n) g.
Proof.
intros x Hx. ap nNum_rect;ir.
rw pow_0. am.
rw pow_S;au. ap Hmon;am.
Qed.

Lemma pow_atend : forall x, inc x g -> forall n, inc n nNum -> 
pow x (oS n) = law (pow x n) x.
Proof.
intros x Hx;ap nNum_rect;ir.
rw pow_S;au. rw pow_0. transitivity x.
ap Hmon;am. symmetry;ap Hmon;am.
ap emptyset_N.
rw pow_S.
rw H0.
cp Hmon. uh H1;ee. rw H3. wr pow_S. rw H0. tv.
am. am. ap pow_inc;am. am. ap oS_nNum;am.
Qed.

Lemma pow_1 : forall x, inc x g -> pow x (oS emptyset) = x.
Proof.
ir;rw pow_S. rw pow_0. ap Hmon;am.
ap emptyset_N.
Qed.

Lemma pow_engendered : forall x n, inc n nNum -> 
Engender.engenders law (doubleton e x) (pow x n).
Proof.
intros x. ap nNum_rect;ir.
rw pow_0. constructor. ap doubleton_l.
rw pow_S;au. ap Engender.engenders_law.
constructor. ap doubleton_r.
am.
Qed.

Lemma pow_engendered_sub : forall h, inc e h -> forall x, inc x h -> forall n, inc n nNum -> 
Engender.engenders law h (pow x n).
Proof.
ir. eapply Engender.engenders_sub_pr. Focus 2.
ap pow_engendered. am. uhg;ir. apply doubleton_or in H2;nin H2;subst;am.
Qed.

Lemma pow_comm_between : forall x, inc x g -> forall y, inc y g -> law x y = law y x -> 
forall n, inc n nNum -> forall m, inc m nNum -> 
law (pow x n) (pow y m) = law (pow y m) (pow x n).
Proof.
intros x Hx y Hy Hc.
assert (Commutative.is_comm_subset law g (tack_on (doubleton x y) e)).
ap Commutative.comm_subset_tack_on_e. am.
uhg;ee. uhg;ir.
apply doubleton_or in H;nin H;subst;am.
uhg;ir.
rwi doubleton_pr H. rwi doubleton_pr H0.
repeat (nin H0;subst);repeat (nin H;subst);au.

apply Commutative.engenders_comm in H;try am.
ir. ap H.
apply Engender.engenders_sub with (doubleton x e).
uhg;ir. apply doubleton_or in H2;nin H2;rw tack_on_inc;subst;au.
left;ap doubleton_l.
ap Engender.engendered_set_pr. rw doubleton_comm. ap pow_engendered.
am.
apply Engender.engenders_sub with (doubleton y e).
uhg;ir. apply doubleton_or in H2;nin H2;rw tack_on_inc;subst;au.
left;ap doubleton_r.
ap Engender.engendered_set_pr. rw doubleton_comm. ap pow_engendered.
am.
Qed.

Lemma pow_comm_law : forall x, inc x g -> forall y, inc y g -> 
law x y = law y x -> 
forall n, inc n nNum -> pow (law x y) n = law (pow x n) (pow y n).
Proof.
intros x Hx y Hy Hc.

ap nNum_rect;ir.
rw pow_0. rw pow_0. rw pow_0. symmetry. ap Hmon;am.

rw pow_S;au. 
rw H0.
rw pow_S;au. rw pow_S;au.
cp pow_inc.
assert (associative law g). am.
transitivity (law (law (x^(oS emptyset)) (y^(oS emptyset))) (law (x ^ n) (y ^ n))).
rw pow_1;au. rw pow_1;au.
assert (inc (oS emptyset) nNum). ap oS_nNum;ap emptyset_N.
transitivity (law (law (x^(oS emptyset)) (x ^ n)) (law (y^(oS emptyset)) (y ^ n))).
Focus 2. rw pow_1;au. rw pow_1;au.
assert (is_lci law g). am.
wr H2;au. wr H2;au. ap uneq.
rw H2;au. rw (pow_comm_between);au.
wr H2;au.
Qed.

(*arithmetic on naturals isn't defined
so we can't prove (x^n)*(x^m) = x^(n+m)*)
End Law.

End Pow.







End Lci. Export Lci.

(*
Module Group_of_Monoid.
Export Quotient.

Section Law.

Variables (g e : E) (law : E2).

Hypothesis is_mon : is_monoid law g e.
Hypothesis is_reg : is_regular law g.
Hypothesis is_comm : commutative law g.

Definition zG0 := product g g.

Definition zEquiv x y := (law (P x) (Q y) = law (P y) (Q x)).

Definition zG := quotient zEquiv zG0.

Definition zE0 := class_of zEquiv zG0 (J e e).

Lemma zE0_inc : inc zE0 zG.
Proof.
uf zG. uf zE0.
ap class_of_in_quotient.
ap product_pair_inc;au.
Qed.

Lemma zEquiv_equivalence : is_equivalence zEquiv zG0.
Proof.
uhg.
ee;uhg;ir. uhg.
tv.
apply product_pr in H;apply product_pr in H0;ee;uh H1.
uhg. symmetry. am.

apply product_pr in H;apply product_pr in H0;apply product_pr in H2;ee.
uh H1;uh H3;ee.
uhg. 
nin is_reg. cp is_comm.
uh H12. rw H12;au. apply H10 with (P y). am. nin is_mon. ee. ap H13;am.
nin is_mon;ap H13;am.
nin is_mon;ee. uh H15.
rw H15;au. rw H3;au.
wr H15;au. cp is_comm.
rwi H16 H1;au. rw H1;au.
symmetry. rw H16;au. wr H15;au. replace (law (Q x) (P y)) with (law (P y) (Q x)).
tv. ap H16; am.
Qed.

Definition zLaw0 x y := J (law (P x) (P y)) (law (Q x) (Q y)).

Notation "x {+} y" := (law x y) (at level 43, no associativity).

Lemma zLaw0_compat : forall x x', inc x zG0 -> inc x' zG0 -> zEquiv x x' -> 
forall y y', inc y zG0 -> inc y' zG0 -> zEquiv y y' -> 
zEquiv (zLaw0 x y) (zLaw0 x' y').
Proof.
ir.
apply product_pr in H;apply product_pr in H0;
apply product_pr in H2;apply product_pr in H3. ee.
uh H1;uh H4. uhg.
uf zLaw0. clpr.
nin is_mon;ee.
wr H15;au. replace (P y{+}(Q x'{+}Q y')) with ((P y{+}Q x'){+}Q y').
replace (P y{+}Q x') with (Q x' {+} P y).
wr H15;au. rw H4.
cp is_comm.
replace (P x{+}(Q x'{+}(P y'{+}Q y))) with ((P x{+}Q x'){+}(P y'{+}Q y)).
rw H1. rw H15;au. rw H16;au. rw H15;au.
rw H15;au. rw H16;au. symmetry. wr H15;au.
rw H16;au. wr H15;au. assert (((Q x{+}Q y){+}P x')=((Q y{+}P x'){+}Q x)).
wr H15;au. rw H17. tv.
wr H15;au. au. wr H15;au.
Qed.

(*
Definition zLaw x y := class_of zEquiv zG0 (zLaw0 )).

Notation "[ x ]" := (class_of zG0 zEquiv x).

Lemma zLaw0_lci : forall x y, inc x zG0 -> inc y zG0 -> inc (zLaw0 x y) zG0.
Proof.
ir. apply product_pr in H;apply product_pr in H0;ee.
apply product_pair_inc. cp is_mon. uh H5;ee. ap H5;am.
cp is_mon;uh H5;ee;ap H5;am.
Qed.

Lemma zLaw_rw : forall x y, inc x zG0 -> inc y zG0 -> 
zLaw [ x ] [ y ] = [ zLaw0 x y ].
Proof.
ir. uf zLaw.
set (x' := (choose (fun i => A (inc i zG0) ([x] = [i])))).
set (y' := (choose (fun i => A (inc i zG0) ([y] = [i])))).
assert (A (inc x' zG0) ([x]=[x'])). ap choose_pr. exists x;tv. ee. am. tv. ee.
assert (A (inc y' zG0) ([y]=[y'])). ap choose_pr. exists y;tv. ee. am. tv. ee.

assert (zEquiv x x').
apply Quotient.equivalent_related with zG0. ap zEquiv_equivalence.
uhg. ee;am.
assert (zEquiv y y').
apply Quotient.equivalent_related with zG0. ap zEquiv_equivalence.
uhg. ee;am.

ap Quotient.related_classes_eq. ap zLaw0_lci;am.
ap zLaw0_lci;am. cp zEquiv_equivalence. uh H7;ee.
ap H8. ap zLaw0_lci;am. ap zLaw0_lci;am.
ap zLaw0_compat;am.
Qed.

Lemma zG_lci : is_lci zLaw zG.
Proof.
uf zG;uhg;ir.
apply Quotient.in_quotient_is_class in H;apply Quotient.in_quotient_is_class in H0.
cp H;cp H0. apply Quotient.class_rep_inc in H1;apply Quotient.class_rep_inc in H2.
cp (Quotient.class_eq_class_of H H1). cp (Quotient.class_eq_class_of H0 H2).
wr H3;wr H4.
assert (sub x zG0). uh H;ee;uh H;ee. am.
assert (sub y zG0). uh H0;ee;uh H0;ee. am.
rw zLaw_rw;au.
ap Quotient.is_class_in_quotient. ap Quotient.class_of_class. ap zLaw0_lci.
ap H5;am. ap H6;am.
Qed.

Lemma zE0_neutre : is_neutre zLaw zG zE0.
Proof.
uf zG.
cp zE0_inc. uhg.
assert (R1 : forall x, inc x zG -> zLaw x zE0 = x).
ir. uf zE0.
apply Quotient.in_quotient_is_class in H0.
cp H0. apply Quotient.class_rep_inc in H1.
cp (Quotient.class_eq_class_of H0 H1).
assert (sub x zG0). uh H0;ee;uh H0;ee. am.
assert (inc (rep x) zG0).
ap H3. am.
ufi zG0 H4.
apply product_pr in H4. ee.
apply pair_recov in H4. uh H4. symmetry in H4.

wr H2. rw zLaw_rw.
uf zLaw0. rw pr1_pair. rw pr2_pair.
cp is_mon. uh H7;ee. uh H8;ee. rw H10. rw H10. wr H4. tv.
am. am. ap H3;am. uf zG0. cp is_mon. ap product_pair_inc; am.

assert (R2 : forall x, inc x zG -> zLaw zE0 x = x).
ir. uf zE0.
apply Quotient.in_quotient_is_class in H0.
cp H0. apply Quotient.class_rep_inc in H1.
cp (Quotient.class_eq_class_of H0 H1).
assert (sub x zG0). uh H0;ee;uh H0;ee. am.
assert (inc (rep x) zG0).
ap H3. am.
ufi zG0 H4.
apply product_pr in H4. ee.
apply pair_recov in H4. uh H4. symmetry in H4.

wr H2. rw zLaw_rw.
uf zLaw0. clear_pr.
cp is_mon. uh H7;ee. uh H8;ee. rw H11. rw H11. wr H4. tv.
am. am. cp is_mon;uf zG0;ap product_pair_inc;am. ap H3;am.

ee;ir. am.
ap R1. am. ap R2;am.
Qed.

Lemma inc_zG : forall x, inc x zG = (exists a, exists b, 
A (inc a (g))
(A (inc b (g))
(x = [J a b]))).
Proof.
uf zG. ir. ap iff_eq;ir.
apply Quotient.in_quotient_is_class in H.
cp H. apply Quotient.class_rep_inc in H0.
cp (Quotient.class_eq_class_of H H0).
assert (sub x zG0). uh H;ee;uh H;ee. am.
assert (inc (rep x) zG0). ap H2;am.
ufi zG0 H3. apply product_pr in H3;ee.
apply pair_recov in H3;uh H3.
exists (P (rep x)). exists (Q (rep x)). ee.
am. am. rw H3;rw H1;tv.

nin H;nin H;ee.
rw H1. ap Quotient.is_class_in_quotient. ap Quotient.class_of_class.
uf zG0;ap product_pair_inc;am.
Qed.

Lemma zG_commutative : commutative zLaw zG.
Proof.
uhg;ir.
rwi inc_zG H;rwi inc_zG H0. nin H;nin H;nin H0;nin H0.
ee. rw H3. rw H4.
rw zLaw_rw. rw zLaw_rw.
uf zLaw0;rw pr1_pair;rw pr2_pair. rw pr1_pair;rw pr2_pair.
cp is_comm. uh H5. rw H5. replace  (x1{+}x3) with (x3 {+} x1). tv.
ap H5. am. am. am. am.
uf zG0;ap product_pair_inc;am.
uf zG0;ap product_pair_inc;am.
uf zG0;ap product_pair_inc;am.
uf zG0;ap product_pair_inc;am.
Qed.

Lemma zG_associative : associative zLaw zG.
Proof.
uhg;ir.
rwi inc_zG H;rwi inc_zG H0;rwi inc_zG H1.
nin H;nin H;nin H0;nin H0;nin H1;nin H1.
ee. subst. cp zLaw0_lci. assert (forall a b, inc a g -> inc b g -> inc (J a b) zG0).
ir. ap product_pair_inc;am.
repeat rw zLaw_rw;au.
uf zLaw0. repeat (rw pr1_pair). repeat (rw pr2_pair). cp is_mon. uh H7;ee.
replace (x0{+}(x2{+}x4)) with ((x0{+}x2){+}x4).
replace (x1{+}(x3{+}x5)) with ((x1{+}x3){+}x5). tv.
uh H9. symmetry. ap H9;am. 
symmetry;ap H9;am.
Qed.

Lemma zG_monoid : is_monoid zLaw zG zE0.
Proof.
uhg;ee. ap zG_lci. ap zE0_neutre. ap zG_associative.
Qed.

Lemma zE0_reps : forall a b, inc a (g) -> inc b (g) -> 
([ J a b ] = zE0) = (a=b).
Proof.
ir. ap iff_eq;ir.
ufi zE0 H1.
assert (zEquiv (J a b) (J e e)).
apply Quotient.equivalent_related with zG0.
ap zEquiv_equivalence. uhg;ee. ap product_pair_inc;am.
cp is_mon;ap product_pair_inc;am. am. uh H2.

rwi pr1_pair H2. rwi pr1_pair H2. rwi pr2_pair H2. rwi pr2_pair H2.
cp is_mon. uh H3;ee. uh H4;ee. rwi H6 H2;rwi H7 H2. am. am. am.
am.

subst.
assert (Quotient.equivalent zG0 zEquiv (J b b) (J e e)).
ap Quotient.related_equivalent. ap product_pair_inc;am.
cp is_mon;ap product_pair_inc;am.
uhg. repeat rw pr1_pair. repeat rw pr2_pair. cp is_mon. uh H1;ee.
uh H2;ee. rw H4;au. rw H5;au.
uh H1. ee. am.
Qed.

Lemma zG_inversing : forall a b, inc a (g) -> inc b (g) -> 
are_inverse zLaw zG zE0 [ J a b ] [ J b a ].
Proof.
ir. assert (inc [ J a b ] zG).
rw inc_zG. exists a;exists b;ee; au.
assert (inc [ J b a ] zG).
rw inc_zG. exists b;exists a;ee; au.

uhg;ee. am. am.
rw zLaw_rw. uf zLaw0. repeat rw pr1_pair;repeat rw pr2_pair.
rw is_comm. rw zE0_reps. tv. cp is_mon;uh H3;ee;ap H3;am.
cp is_mon;uh H3;ee;ap H3;am. am. am. ap product_pair_inc;am.
ap product_pair_inc;am.
rw zLaw_rw. uf zLaw0. repeat rw pr1_pair;repeat rw pr2_pair.
rw is_comm. rw zE0_reps. tv. cp is_mon;uh H3;ee;ap H3;am.
cp is_mon;uh H3;ee;ap H3;am. am. am. ap product_pair_inc;am.
ap product_pair_inc;am.
Qed.

Lemma zG_inverse_of : forall a b, inc a (g) -> inc b (g) -> 
inverse_of zLaw zG zE0 [ J a b ] = [ J b a ].
Proof.
ir. apply inverse_unicity with zLaw zG zE0 [ J a b ].
ap zG_monoid. ap inversible_inverse_of. exists [J b a]. ap zG_inversing.
am. am.
ap zG_inversing;am.
Qed.

Lemma zG_group : is_group zLaw zG zE0.
Proof.
cp zG_monoid.
uhg;ee. am. am. am.
ir. rwi inc_zG H0;nin H0;nin H0.
ee. subst. exists [J x1 x0]. ap zG_inversing.
am. am.
Qed.

Lemma g_in_morphism : Morphisms.is_morphism law g zLaw zG (fun x => [J x e]).
Proof.
uhg. ee. uhg;ir.
rw inc_zG. exists x;exists e. ee. am. cp is_mon;am. tv.
ir.
rw zLaw_rw. uf zLaw0. repeat rw pr1_pair;repeat rw pr2_pair.
cp is_mon. uh H1;ee. uh H2;ee. rw H5. tv. am. ap product_pair_inc;cp is_mon;am. 
ap product_pair_inc;cp is_mon;am.
Qed.

Lemma g_in_inj : Application.injective g zG (fun x => [J x e]).
Proof.
uhg;ee. ap g_in_morphism.
uhg;ir.
assert (zEquiv (J x e) (J y e)).
eapply equivalent_related. ap zEquiv_equivalence.
uhg;ee. ap product_pair_inc;au. ap product_pair_inc;au. am.
uh H2. clear_pr_in H2.
cp is_mon. uh H3;ee. uh H4;ee. rwi H6 H2;au. rwi H6 H2;au.
Qed.

Lemma groupof_isomorph : is_group law g e -> Morphisms.is_isomorphism law g zLaw zG (fun x => [J x e]).
Proof.
ir. uhg. ee. ap g_in_morphism.
cp g_in_morphism.
uhg;ee. am.
uhg;ee. am. uhg;ir.
rwi inc_zG H1. nin H1;nin H1;ee.
subst. exists (law x0 (inverse_of law g e x1)). ee. uh H;ee. ap H.
am. ap group_inverse_inc. uhg;ee;am. am.
ap related_classes_eq.
ap product_pair_inc;au. ap H. am. ap group_inverse_inc;am.
ap product_pair_inc;am.
uhg. clear_pr.
uh H;ee. uh H3;ee.
rw H6;au.
wr H4;au. assert (are_inverse law g e x1 (inverse_of law g e x1)).
ap group_inverse_of;au. uhg;ee;am. uh H8;ee. rw H11.
ap H6;am.
ap group_inverse_inc;au. uhg;ee;am.

ap g_in_inj.
Qed.
*)

End Law.

End Group_of_Monoid.
*)


(*
Module Quotient_groups.
Export Quotient.

Section Law.

Variables (g e g' : E) (law : E2).

Hypotheses (grH : is_group law g e) (sgrH : is_subgroup law g e g').

Definition congruent x y := exists k, (inc k (g') & x = law y k).

Lemma congruence_equiv : is_equivalence congruent g.
Proof.
uhg;ee;uhg. ir. uhg. exists e. ee. am.
symmetry. cp grH. uh H0;ee. uh H1;ee. ap H4;am.

ir. uh H1;nin H1. ee.
uhg. exists (inverse_of law g e x0).
ee.
rewrite subgroup_inverse_eq with law g e g' x0. ap group_inverse_inc. am.
am. am. am. am.
rw H2. assert (are_inverse law g e x0 (inverse_of law g e x0)).
ap group_inverse_of. am. cp sgrH. uh H3;ee. ap H3;am.
cp grH. uh H4;ee. wr H6;au. uh H3;ee. rw H9.
uh H5;ee;symmetry. ap H11;au.

ir. uh H1;uh H3. nin H1;nin H3;ee.
subst. uhg. exists (law x1 x0).
ee. cp sgrH. uh H4;ee. uh H5;ee. ap H5. am. am.
cp grH. uh H4;ee. rw H6;au.
cp sgrH. uh H8;ee;ap H8;am.
cp sgrH. uh H8;ee;ap H8;am.
Qed.

Definition QuotGroup := Im (class_of congruent g) g.

Notation "[ x ]" := (class_of congruent g x).

Definition is_normal_subgroup b := 
A (is_subgroup law g e b)
(forall n, inc n (b) -> forall x, inc x (g) ->
inc (law x (law n (inverse_of law g e x))) (b)).

Lemma commutative_all_normal : commutative law g -> forall b, is_subgroup law g e b -> is_normal_subgroup b.
Proof.
ir.
uhg. ee. am. ir. rw H. cp grH.
uh H3;ee. wr H5;au. assert (are_inverse law g e x (inverse_of law g e x)).
ap group_inverse_of;am. uh H7;ee. rw H10. uh H4;ee. rw H11. am.
uh H0;ee. ap H0;am. uh H0;ee;ap H0;am.
ap group_inverse_inc. am. am. am.
cp grH. uh H3;ee;ap H3. uh H0;ee;ap H0;am. ap group_inverse_inc.
am. am.
Qed.

Lemma law_congruence_compat : is_normal_subgroup g' -> 
forall x y, inc x (g) -> inc y (g) -> congruent x y -> 
forall x' y', inc x' (g) -> inc y' (g) -> congruent x' y' -> 
congruent (law x x') (law y y').
Proof.
ir. uh H2;uh H5;nin H2;nin H5;ee. subst.
uhg. uh H;ee.
exists (law (law (inverse_of law g e y') (law x0 y')) x1).
set (y0 := inverse_of law g e y'). replace y' with (inverse_of law g e y0).
ee. uh H;ee. uh H7;ee;ap H7. ap H6. am. uf y0. ap group_inverse_inc. am. am.
am.
uf y0. wr inverse_inverse;au.
cp grH. uh H7;ee. symmetry.
replace (law (law y y') (law (law (inverse_of law g e y') (law x0 y')) x1)) with
(law (law y (law y' (inverse_of law g e y'))) (law (law x0 y') x1)).
assert (are_inverse law g e y' (inverse_of law g e y')). ap group_inverse_of;au.
uh H11;ee. rw H13. uh H8;ee. rw H15;au.
rw H9;au. rw H9;au. rw H9;au. ap H. am.
ap H;am. ap H7. ap H;am. am. ap H;am.
uh H;ee.
wr H9;au. wr H9;au. wr H9;au. wr H9;au. wr H9;au. wr H9;au.
ap group_inverse_inc;am. ap H7;au. ap H7;au.
ap group_inverse_inc;am. ap group_inverse_inc;am.
ap H7;au. ap group_inverse_inc;am.
uf y0. symmetry. ap inverse_inverse. am.
am.
Qed.

Definition QuotLaw x y := [ law (rep x) (rep y) ].

Lemma QuotLaw_rw : forall norm : is_normal_subgroup g', forall x y, inc x (g) -> inc y (g) ->
QuotLaw [ x ] [ y ] = [ law x y ].
Proof.
ir. uf QuotLaw.
assert (inc (rep [ x]) (g)).
assert (is_class congruent g [x]).
ap class_of_class. am. apply class_rep_inc in H1.
assert (sub [x] (g)).
ap class_of_sub. au. ap congruence_equiv.
assert (inc (rep [y]) (g)).
assert (is_class congruent g [y]).
ap class_of_class. am. apply class_rep_inc in H2.
assert (sub [y] (g)).
ap class_of_sub. au. ap congruence_equiv.

ap related_classes_eq. cp grH. uh H3;ee. ap H3. am. am.
cp grH. uh H3;ee;ap H3;au.
ap law_congruence_compat.
am. am. am. apply equivalent_related with (g).
ap congruence_equiv. uhg. ee. am. am.
ap class_of_rep. ap class_of_in_quotient. am.
am. am.  apply equivalent_related with (g).
ap congruence_equiv. uhg. ee. am. am.
ap class_of_rep. ap class_of_in_quotient. am.
Qed.

Lemma QuotGroup_is_group : is_normal_subgroup g' -> is_group QuotLaw QuotGroup [ e ].
Proof.
ir.
uhg. assert (is_lci QuotLaw QuotGroup).
uf QuotGroup;uhg;ir.
apply Image.ex in H0;apply Image.ex in H1;nin H0;nin H1.
ee. subst.
rw QuotLaw_rw. apply Image.incl. cp grH. uh H2;ee. ap H2. am. am.
am. am. am.
ee. am. assert (inc [e] (QuotGroup)).
ap Image.incl. cp grH;am.
uhg;ee. am.
ir. apply Image.ex in H2. nin H2;ee;subst.
rw QuotLaw_rw. cp grH. uh H3;ee;uh H4;ee. rw H7. tv.
am. am. am.
cp grH;am.
ir. apply Image.ex in H2;nin H2;ee;subst.
rw QuotLaw_rw. cp grH. uh H3;ee;uh H4;ee. rw H8. tv.
am. am. cp grH;am. am.

uhg;ir.
apply Image.ex in H1;apply Image.ex in H2;apply Image.ex in H3.
nin H1;nin H2;nin H3. ee;subst.
cp grH. uh H4;ee. rw QuotLaw_rw;au. rw QuotLaw_rw;au. rw QuotLaw_rw;au. rw QuotLaw_rw;au.
rw H6;au.

ir.
apply Image.ex in H1;nin H1;ee;subst. exists [inverse_of law g e x0].
assert (are_inverse law g e x0 (inverse_of law g e x0)).
ap group_inverse_of. am. am.
uhg;ee. ap Image.incl;au.
ap Image.incl. am.
rw QuotLaw_rw. uh H2;ee. rw H4. tv.
am. am. am.
rw QuotLaw_rw. uh H2;ee. rw H5. tv.
am. am. am.
Qed.

End Law.

End Quotient_groups.
Export Quotient_groups.
*)

Module Cosets.

Section Law.

Variables (a e : E) (pl : E2).

Hypothesis (grH : is_group pl a e).

Definition coset_of x h := Z a (fun y => exists z, inc z h & y = pl x z).
Definition rcoset_of h x := Z a (fun y => exists z, inc z h & y = pl z x).

Definition is_normal_subgroup h :=
A (is_subgroup pl a e h)
(forall x, inc x h -> forall y, inc y a -> inc (pl y (pl x (inverse_of pl a e y))) h).

Lemma normal_subgroup_cosets_rw : forall h, is_subgroup pl a e h -> 
is_normal_subgroup h = (forall x, inc x a -> coset_of x h = rcoset_of h x).
Proof.
ir;ap iff_eq;ir.
ap extensionality;uhg;ir.

ufi coset_of H2;Ztac. ap Z_inc. am.
nin H3;ee;subst. uh H0;ee.
exists (pl (pl (inverse_of pl a e x0) (pl x0 (pl x x0))) (inverse_of pl a e x)).
ee.
assert (are_inverse pl a e x0 (inverse_of pl a e x0)).
ap group_inverse_of;au. ap H;am.
uh H5;ee. cp grH. uh H9;ee.
rw H11;au. rw H8. uh H10;ee.
rw H14;au. wr H11;au. ap group_inverse_inc;am.
assert (are_inverse pl a e x0 (inverse_of pl a e x0)). ap group_inverse_of;au.
ap H;am. assert (are_inverse pl a e x (inverse_of pl a e x)).  ap group_inverse_of;am.
uh H6;uh H5;ee.
cp grH. uh H13;ee.
rw H15;au. rw H12. uh H14;ee. rw H18;au.
wr H15;au. rw H10;au. rw H17;au.

ufi rcoset_of H2;Ztac;au.
ap Z_inc. am.
nin H3;ee;subst.
exists (pl (inverse_of pl a e x) (pl x0 (pl x (pl (inverse_of pl a e x0) x0)))).
ee.
assert (are_inverse pl a e x0 (inverse_of pl a e x0)). ap group_inverse_of;au.
ap H;am. uh H4;ee. cp grH.
uh H8;ee. rw H10;au. rw H7. uh H9;ee.
rw H12;au. set (x' := inverse_of pl a e x). replace x with (inverse_of pl a e x').
wr H10;au. ap H0. am. 
uf x'. ap group_inverse_inc;au.
uf x'. ap group_inverse_inc;au.
uf x'. wr inverse_inverse;au.
uf x'. wr inverse_inverse;au.
ap group_inverse_inc;au.
assert (are_inverse pl a e x (inverse_of pl a e x)). ap group_inverse_of;au.
assert (are_inverse pl a e x0 (inverse_of pl a e x0)). ap group_inverse_of;au.
ap H;am.

uh H4;uh H5;ee;cp grH.
uh H12;ee.
rw H14;au. rw H10. uh H13;ee.
rw H17;au. rw H9. rw H16;au.

uhg;ee. am.
ir.
cp grH. uh H3;ee. rw H5;au.
assert (inc (pl y x) (coset_of y h)).
ap Z_inc;au. ap H3. am. ap H;am.
exists x. ee. am. tv.
rwi H0 H7. ufi rcoset_of H7. Ztac;au.
nin H8. ee. rw H9. wr H5;au.
assert (are_inverse pl a e y (inverse_of pl a e y)). ap group_inverse_of;au.
uh H10;ee. rw H12. uh H4;ee.
rw H14;au. ap H;am. ap H;am.
ap group_inverse_inc;au. am. ap H;am.
ap group_inverse_inc;am.
Qed.

End Law.

End Cosets.
Export Cosets.

Module Inner_lci.

Section Law.

Variables (g : E) (law : E2).

Hypothesis Hlci : is_lci law g.

Notation innerLaw := (Im2 law).

Lemma innerLaw_rw : forall a b x, inc x (innerLaw a b) = (exists k, exists l, inc k a & inc l b & x = law k l).
Proof.
ap Im2_rw.
Qed.

Lemma innerLaw_inc : forall a b x y, inc x a -> inc y b -> 
inc (law x y) (innerLaw a b).
Proof.
ir. rw innerLaw_rw. exists x;exists y;ee;au.
Qed.

Lemma innerLaw_lci : is_lci innerLaw (powerset g).
Proof.
uhg;ir.
rw powerset_rw.
rwi powerset_rw H. rwi powerset_rw H0.
uhg;ir.
rwi innerLaw_rw H1. nin H1;nin H1;ee.
subst. ap Hlci. au. au.
Qed.

Lemma innerLaw_assoc : associative law g -> associative innerLaw (powerset g).
Proof.
ir.
uhg;ir.
rwi powerset_rw H0;rwi powerset_rw H1;rwi powerset_rw H2.

ap extensionality;uhg;ir.
rwi innerLaw_rw H3;nin H3;nin H3;ee.
subst. rwi innerLaw_rw H4;nin H4;nin H4;ee;subst.

rw H;au.
ap innerLaw_inc;au. ap innerLaw_inc;au.

rwi innerLaw_rw H3;nin H3;nin H3;ee.
subst. rwi innerLaw_rw H3;nin H3;nin H3;ee.
subst.
wr H;au.
ap innerLaw_inc;try am.
ap innerLaw_inc;am.
Qed.

Lemma innerLaw_comm : commutative law g -> commutative innerLaw (powerset g).
Proof.
ir;uhg;ir.
ap extensionality;uhg;ir.

rwi innerLaw_rw H2;nin H2;nin H2;ee;subst.

rw H. ap innerLaw_inc;am.
rwi powerset_rw H0;au.
rwi powerset_rw H1;au.

rwi powerset_rw H0;rwi powerset_rw H1.
rwi innerLaw_rw H2;nin H2;nin H2;ee;subst.
rw H;au; ap innerLaw_inc;am.
Qed.

Lemma innerLaw_neutre : forall e, is_neutre law g e -> is_neutre innerLaw (powerset g) (singleton e).
Proof.
ir.
uhg;ee.
rw powerset_rw. uhg;ir;apply singleton_eq in H0.
subst;am.

ir. rwi powerset_rw H0.
ap extensionality;uhg;ir.
rwi innerLaw_rw H1;nin H1;nin H1;ee;subst.
apply singleton_eq in H2;subst.
uh H;ee. rw H2;au.

uh H;ee. wr (H2 a);au.
ap innerLaw_inc;au.
ap singleton_inc.

ir. rwi powerset_rw H0.
ap extensionality;uhg;ir.
rwi innerLaw_rw H1;nin H1;nin H1;ee;subst.
apply singleton_eq in H1;subst.
uh H;ee. rw H3;au.

uh H;ee. wr (H3 a);au.
ap innerLaw_inc;au.
ap singleton_inc.
Qed.

End Law.

Lemma innerLaw_monoid : forall law g e, is_monoid law g e -> 
is_monoid (Im2 law) (powerset g) (singleton e).
Proof.
ir.
uhg;ee. ap innerLaw_lci. am.
ap innerLaw_neutre. am.
ap innerLaw_assoc. am.
Qed.

Ltac innerLaw_destruct H := rwi innerLaw_rw H;nin H;nin H;ee.

Lemma inner_subgroup : forall law g e, is_group law g e -> forall Hc : commutative law g,
forall h h', is_subgroup law g e h -> is_subgroup law g e h' -> is_subgroup law g e (Im2 law h h').
Proof.
ir.
ap subgroup_show. am.
wr powerset_rw;ap innerLaw_lci;[ am |
rw powerset_rw;am | rw powerset_rw;am].

exists e.
replace e with (law e e).
ap innerLaw_inc. am. am.
ap H. uh H;ee. uh H2;ee. am.

ir. innerLaw_destruct H2;innerLaw_destruct H3;subst.
replace (law (law x0 x1) (law x2 x3)) with (law (law x0 x2) (law x1 x3)).
ap innerLaw_inc. ap H0;am. ap H1;am.

uh H;ee.
assert (sub h g). am.
assert (sub h' g). am.
wr H7;au. wr H7;au.
ap f_equal.
rw H7;au. rw H7;au.
rw Hc;au. symmetry.
rw Hc;au. ap f_equal. ap Hc;au.

ir.
innerLaw_destruct H2;subst.
assert (sub h g). am.
assert (sub h' g). am.
rw group_inverse_of_law;au.
cp (group_inverse_of H (H4 x0 H2)).
cp (group_inverse_of H (H5 x1 H3)).
rw Hc;try am.

ap innerLaw_inc;[rw (subgroup_inverse_eq H H0) | rw (subgroup_inverse_eq H H1)];
au;ap group_inverse_inc;am.
Qed.

End Inner_lci. Export Inner_lci.


Module Ordered_lci.
Export Order.

Definition is_ltranslation_invariant (r:E2P) pl a := forall x, inc x a -> 
forall y, inc y a -> forall z, inc z a -> 
r y z -> r (pl x y) (pl x z).
Definition is_rtranslation_invariant (r:E2P) pl a := forall x, inc x a -> 
forall y, inc y a -> forall z, inc z a -> 
r y z -> r (pl y x) (pl z x).

Definition is_translation_invariant r pl a := A ( is_rtranslation_invariant r pl a) 
( is_ltranslation_invariant r pl a).

Definition is_compatible (r:E2P) pl a := forall x, inc x a -> forall x', inc x' a -> 
r x x' -> 
forall y, inc y a -> forall y', inc y' a -> 
r y y' -> 
r (pl x y) (pl x' y').

Lemma invariant_compat : forall r pl a, is_order r a -> is_lci pl a -> 
is_translation_invariant r pl a -> is_compatible r pl a.
Proof.
ir;uhg;ir.
 eapply H. au. Focus 2. ap H1. am. am.
Focus 2. am. au. am. au. ap H1;au.
Qed.

Lemma invariant_transitive_compat : forall r pl a, transitiveT r a -> is_lci pl a -> 
is_translation_invariant r pl a -> is_compatible r pl a.
Proof.
ir;uhg;ir.
 eapply H. au. Focus 2. ap H1. am. am.
Focus 2. am. au. am. au. ap H1;au.
Qed.

Lemma compat_invariant : forall (r:E2P) pl a, is_order r a -> is_compatible r pl a -> is_translation_invariant r pl a.
Proof.
ir;uhg;ee;uhg;ir;ap H0;try am.
ap H;am. ap H;am. 
Qed.

Definition is_ordered_lci r pl a := A (is_order r a) (A (is_lci pl a)
(is_compatible r pl a)).

Definition is_ordered_monoid r pl a e := A (is_order r a) (A (is_monoid pl a e)
(is_compatible r pl a)).

Definition is_ordered_group r pl a e := A (is_order r a) (A (is_group pl a e)
(is_compatible r pl a)).

Definition is_order_lregular (r:E2P) pl a := forall x, inc x a -> 
forall y, inc y a -> forall y', inc y' a -> r (pl x y) (pl x y') -> 
r y y'.
Definition is_order_rregular (r:E2P) pl a := forall x, inc x a -> 
forall y, inc y a -> forall y', inc y' a -> r (pl y x) (pl y' x) -> 
r y y'.
Definition is_order_regular (r:E2P) (pl:E2) (a:E)  : Prop.
ap A. ap is_order_lregular;am. ap is_order_rregular;am. 
Defined.

Lemma ordered_group_order_regular : forall r pl a e, is_ordered_group r pl a e -> 
is_order_regular r pl a.
Proof.
ir;uhg;ee;uhg;ir.
assert (r (pl (inverse_of pl a e x) (pl x y)) (pl (inverse_of pl a e x) (pl x y'))).
ap H. ap group_inverse_inc;am.
ap group_inverse_inc;am.
ap H;ap group_inverse_inc;am.
ap H;am. ap H;am.
am.
uh H;ee. uh H5;ee.
rwi H8 H4. rwi H8 H4.
uh H7;ee.
edestruct group_inverse_of. uhg;ee;try am;uhg;ee;am.
ap H0.
ee. rwi H15 H4.
rwi H11 H4;au. rwi H11 H4;au.
ap group_inverse_inc. uhg;ee;am.
am. am. am. ap group_inverse_inc. uhg;ee;am.
am. am. am.

edestruct group_inverse_of. am.
ap H0.
ee.
assert (r (pl (pl y x) (inverse_of pl a e x)) (pl (pl y' x) (inverse_of pl a e x))).
ap H;try am;repeat ap H;au.
assert (associative pl a). am. wri H9 H8;au. wri H9 H8;au.
rwi H6 H8. assert (is_neutre pl a e). am.
uh H10;ee. rwi H11 H8;au. rwi H11 H8;au.
Qed.

End Ordered_lci.

