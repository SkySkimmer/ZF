Set Implicit Arguments.
Unset Strict Implicit.

Module Tactics1.
Ltac ir := intros.

Ltac rw u := rewrite u.
Ltac rwi u h := rewrite u in h.

Ltac wr u := rewrite <- u.
Ltac wri u h := rewrite <- u in h.

Ltac ap h := apply h.

Ltac EasyAssumption :=
  match goal with
  | id1:(?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8) |-
  (?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8) =>
      exact id1
  | id1:(?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7) |- (?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7) =>
      exact id1
  | id1:(?X1 ?X2 ?X3 ?X4 ?X5 ?X6) |- (?X1 ?X2 ?X3 ?X4 ?X5 ?X6) =>
      exact id1
  | id1:(?X1 ?X2 ?X3 ?X4 ?X5) |- (?X1 ?X2 ?X3 ?X4 ?X5) =>
      exact id1
  | id1:(?X1 ?X2 ?X3 ?X4) |- (?X1 ?X2 ?X3 ?X4) =>
      exact id1
  | id1:(?X1 ?X2 ?X3) |- (?X1 ?X2 ?X3) => exact id1
  | id1:(?X1 ?X2) |- (?X1 ?X2) => exact id1
  | id1:?X1 |- ?X2 => ap id1
  | _ => fail
  end.

Ltac am := solve [ EasyAssumption | assumption ].




Ltac au := first [ solve [ EasyAssumption ] | auto ].
Ltac eau := eauto. 
Ltac tv := trivial.
Ltac sy := symmetry  in |- *.

Ltac uf u := unfold u in |- *. Ltac ufi u h := unfold u in h.
Ltac ufa u := unfold u in *.

Ltac nin h := induction h.




Ltac CompareTac a b :=
  assert (toclear : a = a); [ exact (refl_equal b) | clear toclear ].

Ltac UnfoldHead1 h :=
  match constr:h with
  | (?X1 ?X2) => unfold X1 in h
  | _ => fail
  end.

(*** we don't actually want to unfold certain things ***)
Ltac Good_Unfold g h :=
  match constr:g with
  | _ => unfold g in h
  end.

Ltac Unfold_Head_R g h :=
  match constr:g with
  | (?X1 _ _ _ _ _ _ _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _ _ _ _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _ _ _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _ _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _ _) => Good_Unfold X1 h
  | (?X1 _ _ _) => Good_Unfold X1 h
  | (?X1 _ _) => Good_Unfold X1 h
  | (?X1 _) => Good_Unfold X1 h
  | ?X1 => Good_Unfold X1 h
  end.


Ltac Unfold_Head h :=
  match goal with
  | id1:?X1 |- _ => CompareTac id1 h; Unfold_Head_R X1 h
  | _ => fail
  end.

Ltac Exploit h :=
  match goal with
  | id1:?X1 |- _ =>
      CompareTac id1 h; assert X1; [ am | Unfold_Head h; Exploit h ]
  | _ => idtac
  end.

Ltac xlt h := Exploit h.

Definition DONE (A : Type) (a : A) := a.
Definition TODO (A : Type) (a : A) := a.

Ltac TodoAll :=
  match goal with
  | id1:?X1 |- _ =>
      match constr:X1 with
      | (TODO _) => fail
      | _ => change (TODO X1) in id1; TodoAll
      end
  | _ => idtac
  end.

Definition CheckProp (P : Prop) := P.

Ltac CheckPropTac P := assert (toclear : CheckProp P); [ am | clear toclear ].

Infix "&":= and (right associativity, at level 100).

Ltac Deconj :=
  match goal with
  |  |- (and _ _) => ap conj; [ Deconj | Deconj ]
  |  |- (_ & _) => ap conj; [ Deconj | Deconj ]
  |  |- (and _ _) => ap conj; [ Deconj | Deconj ]
  |  |- (_ /\ _) => ap conj; [ Deconj | Deconj ]
  |  |- _ => au
  end.

Ltac EasyDeconj :=
  match goal with
  |  |- (and _ _) => ap conj; [ EasyDeconj | EasyDeconj ]
  |  |- (_ & _) => ap conj; [ EasyDeconj | EasyDeconj ]
  |  |- (and _ _) => ap conj; [ EasyDeconj | EasyDeconj ]
  |  |- (_ /\ _) => ap conj; [ EasyDeconj | EasyDeconj ]
  |  |- _ => idtac
  end.




Ltac Expand :=
  match goal with
  | id1:(and ?X1 ?X2) |- _ =>
      nin id1; Expand
  | id1:(?X1 & ?X2) |- _ => nin id1; Expand
  | id1:(and ?X1 ?X2) |- _ => nin id1; Expand
  | id1:(?X1 /\ ?X2) |- _ => nin id1; Expand
  |  |- _ => Deconj
  end.



(*** we write a tactic which is like Pose but which is anonymous ***)
Ltac Remind u :=
  set (recalx := u);
   match goal with
   | recalx:?X1 |- _ => assert X1; [ exact recalx | clear recalx ]
   end.

Ltac cp := Remind. 


Ltac EasyExpand :=
  match goal with
  | id1:(and ?X1 ?X2) |- _ =>
      nin id1; EasyExpand
  | id1:(?X1 /\ ?X2) |- _ => nin id1; EasyExpand
  | id1:(?X1 /\ ?X2) |- _ => nin id1; EasyExpand
  |  |- _ => EasyDeconj
  end.


Ltac ee := EasyExpand.

Ltac xd := Expand.




Ltac PreExplode n :=
  match constr:n with
  | 0 => idtac
  | (S ?X1) =>
      match goal with
      | id1:?X2 |- _ =>
          CheckPropTac X2;
           match constr:X2 with
           | (DONE ?X3) => fail
           | _ =>
               assert (DONE X2);
                [ unfold DONE in |- *; am
                | Unfold_Head id1; EasyExpand; PreExplode X1 ]
           end
      | _ => idtac
      end
  end.

Ltac ClearDone :=
  match goal with
  | id1:(DONE ?X1) |- _ => unfold DONE in id1; ClearDone
  | _ => idtac
  end.



Ltac Exp := PreExplode 5; ClearDone.
Ltac Expl := PreExplode 10; ClearDone. 
Ltac Explode := PreExplode 100; ClearDone.



Ltac CleanUp :=
  match goal with
  | id1:?X1,id2:?X1 |- _ => CheckPropTac X1; clear id2; CleanUp
  | _ => idtac
  end.

Ltac xde := Explode.
Ltac cx := Explode; CleanUp.

(***** we would like a general Cycle construction (can we parametrize tactics over tactics???) ***)


Ltac sh x := first
 [ apply ex_intro with x
 | apply ex_intro with x ].


Lemma seq_deconj : forall P Q : Prop, P -> (P -> Q) -> (P & Q). 
ir. xd. Qed. 

Ltac dj :=
  match goal with
  |  |- (and ?X1 ?X2) => ap seq_deconj; ir; dj
  |  |- (?X1 & ?X2) => ap seq_deconj; ir; dj
  | _ => idtac
  end. 



Ltac MiddleDeconj :=
  match goal with
  |  |- (and _ _) =>
      ap conj; [ MiddleDeconj | MiddleDeconj ]
  |  |- (_ /\ _) => ap conj; [ MiddleDeconj | MiddleDeconj ]
  |  |- (_ /\ _) => ap conj; [ MiddleDeconj | MiddleDeconj ]
  |  |- _ => first
  [ solve [ trivial | EasyAssumption | sy; EasyAssumption ] | idtac ]
  end.

Ltac MiddleExpand :=
  match goal with
  | id1:(and ?X1 ?X2) |- _ =>
      nin id1; MiddleExpand
  | id1:(?X1 /\ ?X2) |- _ => nin id1; MiddleExpand
  | id1:(?X1 /\ ?X2) |- _ => nin id1; MiddleExpand
  |  |- _ => MiddleDeconj
  end.

Ltac xe := MiddleExpand.

Definition type_of (T : Type) (t : T) := T.

Ltac Copy a :=
  assert (type_of a);
   [ exact a | match goal with
               | id1:(type_of _) |- _ => ufi type_of id1
               end ].

Ltac ufk a b := Copy b; ufi a b. Ltac uh a := red in a.
(*** replaces Unfold_Head a. as mentionned by Hugo ***)

Ltac uhg := red in |- *. 
(*** Match Context With 
[|-(?1 ? ? ? ? ? ? ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ? ? ? ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ? ? ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ? ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ? ?)] -> Unfold ?1 |
[|-(?1 ? ?)] -> Unfold ?1 |
[|-(?1 ?)] -> Unfold ?1 |
_-> Idtac.
***)

Ltac util a:=
match (type of a) with 
| (?X1 -> ?X2 -> ?X3 -> ?X4 -> ?X5 -> ?X6) => assert X6; [apply a |idtac]
| (?X1 -> ?X2 -> ?X3 -> ?X4 -> ?X5) => assert X5; [apply a |idtac]
| (?X1 -> ?X2 -> ?X3 -> ?X4) => assert X4; [apply a |idtac]
| (?X1 -> ?X2 -> ?X3) => assert X3; [apply a |idtac]
| (?X1 -> ?X2) => assert X2; [apply a |idtac]
| _ => fail
end. 


Lemma uneq : forall A B (f:A->B) x y,
x = y -> f x = f y.
Proof.
ir. rw H; tv. 
Qed. 

Lemma uneq2 : forall A B C (f : A -> B -> C) x x', x=x' -> forall y y', y=y' -> 
f x y = f x' y'.
Proof.
ir. rw H. ap uneq. am.
Qed.



Ltac LookUpErasing :=
match goal with 
| id1 : ?X1 |- _ => 
first [exact id1 | uh id1; ee; try tv; try am|clear id1 ]
| _ => fail
end. 

Ltac lu := 
LookUpErasing; lu. 
(*** not all that efficient for time so don't use too often ***)

End Tactics1.
Export Tactics1.

Module Utilities.

Lemma and_P : forall a b, and a b -> a.
Proof.
ir. nin H;am.
Qed.

Lemma and_Q : forall a b, and a b -> b.
Proof.
ir. nin H;am.
Qed.

Inductive PropGuard : Prop -> Prop :=
 Pguard : forall P:Prop, P -> PropGuard P
.

Lemma PropGuard_use : forall P, PropGuard P -> P.
Proof.
ir. nin H. am.
Qed.

End Utilities. Export Utilities.
