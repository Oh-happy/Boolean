(*********************************************)
(******* 基于一阶逻辑的布尔代数模型的形式化 *******)
(*********************************************)

Require Import Coq.Sets.Ensembles. 
Require Import Coq.Logic.Epsilon.
Require Import Coq.Logic.Classical.

(* Ensembles库 *)
Notation "a ∈ A" := (In _ A a) (at level 10).
Notation "B ∪ C" := (Union _ B C) 
                     (at level 65, left associativity).
Notation "[ a ]" := (Singleton _ a)
                    (at level 0, right associativity).
Notation "A ⊆ B" := (Included _ A B) (at level 70).
Notation "A ~ B" := (Setminus _ A B)
                    (at level 0, right associativity).
Notation "B ∩ C" := (Intersection _ B C) 
                    (at level 65, left associativity).

(* 集合性质 *)
Corollary UnionI : forall {U} (a: U) B C, 
  a ∈ (B ∪ C) <-> a ∈ B \/ a ∈ C.
Proof. 
  split; intros; destruct H; eauto with sets. 
Qed.

Corollary Single : forall {U} (a x: U), a ∈ [ x ] <-> a = x.
Proof. split; intros. destruct H; auto. rewrite H. split. Qed.

Global Hint Resolve UnionI Single: sets.

Corollary commu : forall {U} (A B: Ensemble U), A ∪ B = B ∪ A.
Proof.
  intros. apply Extensionality_Ensembles; red; intros; 
  split; red; intros.
  - destruct H. right; auto. left;auto.
  - destruct H. right; auto. left;auto.
Qed.

Corollary assoc : forall {U} (A B C: Ensemble U), 
  A ∪ B ∪ C = A ∪ (B ∪ C).
Proof.
  intros. apply Extensionality_Ensembles; red; 
  intros; split; red; intros.
  - destruct H. 
    + destruct H. left. auto. right; left; auto.
    + right; right; auto.
  - destruct H.
    + left; left; auto.
    + destruct H. left; right; auto. right; auto.
Qed.

(* 逻辑性质 *)
(* 排中律 *)
Theorem excluded : forall p, {p} + {~p}.
Proof.
  intros. assert { x:bool | if x then p else ~p }.
  { apply constructive_indefinite_description.
    destruct (classic p).
    - exists true. auto.
    - exists false. auto. }
  destruct H,x; auto.
Qed.

(* 一阶逻辑基本语法 *)
(* 一阶语言符号 *)
(*个体变元*)
Inductive Var : Set :=
  | X : nat -> Var.

(*个体常元*)
Inductive Con : Set :=
  | C : nat -> Con.

(*运算符*)
(* Inductive Fun : Set :=
  | F : nat -> Fun. *)
  
Inductive Fun : Set :=
  | F : nat -> nat -> Fun.

(*谓词*)
(* Inductive Rel : Set :=
  | R : nat -> Rel. *)

Inductive Rel : Set :=
  | R : nat -> nat -> Rel.

(* 元数（arity）函数 *)
Definition arity_f (f : Fun) : nat :=
  match f with
  | F a b => a
  end.

Definition arity_r (r : Rel) : nat :=
  match r with
  | R a b => a
  end.
(* Axiom arity_r : Rel -> nat. *)
Definition arity_F f := S (arity_f f).
Definition arity_R r := S (arity_r r).

(* 项 *)
Inductive vector (A: Type) : nat -> Type :=
  |vector0 : vector A 0
  |vectorcons : forall (h:A) (n:nat), vector A n -> vector A (S n).

Inductive term : Set :=
  | Tvar : Var -> term
  | Tcon : Con -> term
  | Tfun : forall f: Fun, vector term (arity_F f) -> term.
  
Notation "x :: l" := (vectorcons _ x _ l).
Notation "[]" := (vector0 term).

(* 公式 *)
Section Formula.

Inductive Formula :=
  | equality : term -> term -> Formula
  | atomic : forall (r: Rel), vector (term) (arity_R r) -> Formula
  | Not : Formula -> Formula
  | Contain : Formula -> Formula -> Formula 
  | Forall : Var -> Formula -> Formula.

(* 其他符号 *)
Definition Inequality t1 t2 := Not (equality t1 t2). 
(* ∨ *)
Definition Disjunction p q := Contain (Not p) q.
(* ∧ *)
Definition Conjunction p q := Not (Contain p (Not q)).
(* ↔ *)
Definition Equivalent p q := Conjunction (Contain p q) (Contain q p).

Definition Exists x p := Not (Forall x (Not p)).

End Formula.

Notation "t1 ≌ t2" := (equality t1 t2)(at level 2).

Notation "¬ q" := (Not q)(at level 5,right associativity).

Notation "p → q" := (Contain p q)
                    (at level 11,right associativity).

Notation "∀ x , p" := (Forall x p) 
                      (at level 7, right associativity).

Notation " p ∨ q " := (Disjunction p q)
                      (at level 11, right associativity).
 
Notation " p ∧ q " := (Conjunction p q)
                      (at level 9, right associativity).

Notation " p ↔ q " := (Equivalent p q)
                      (at level 12, right associativity).

Notation "∃ x , p" := (Exists x p)
                      (at level 8, right associativity).

(* 语义 *)
Section structure.

Variable M : Type.

Definition I_c := Con -> M.
Definition I_f := forall (f: Fun), vector M (arity_F f) -> M.
Definition I_R := forall (r: Rel), vector M (arity_R r) -> Prop. 

(* 赋值 *)
Definition value := Var -> M.

(* x重新赋值为m *)
Definition value_v (v: value) (x: Var) (m: M) := 
  fun (y: Var) => match (excluded (y = x)) with
                   | left _ => m
                   | right _ => v y
                  end.

(*项t的赋值*)
Definition map_vector {A} {B} (f: A -> B) : forall {n} 
  (v: vector A n), vector B n :=
  fix map_fix {n} (v: vector A n) : vector B n := 
    match v with
    | vector0 _ => vector0 _
    | vectorcons _ a _ v' => vectorcons _ (f a) _ (map_fix v')
    end.

Fixpoint value_term (v: value) (Ic : I_c)(If: I_f) (t: term) : M :=
  match t with
  | Tvar s => v s
  | Tcon c => Ic c
  | Tfun f q => If f (map_vector (value_term v Ic If) q)
  end.

(* 塔斯基语义 可满足关系 ⊨ *)
Fixpoint satisfy_R (v: value) (Ic: I_c)(If: I_f)(IR: I_R)(p: Formula) 
  {struct p} : Prop :=
  match p with
  | equality t1 t2 => value_term v Ic If t1 = value_term v Ic If t2
  | atomic r v1 => IR r (map_vector (value_term v Ic If ) v1)
  | Not q => ~ satisfy_R v  Ic If IR q
  | Contain q r => (~ satisfy_R v Ic If IR q) \/ (satisfy_R v Ic If IR r)
  | Forall x q => forall (m: M), satisfy_R (value_v v x m) Ic If IR q 
  end.
End structure.

Definition satisfy_Formula M Ic' If' IR' p := 
  forall v, satisfy_R M v Ic' If' IR' p.
  

(********************************************) 
(*************** 布尔代数 ********************)
(********************************************)

(* 基本符号 *)
Definition c0 := Tcon (C 0).
Definition c1 := Tcon (C 1).

Definition fs := F 0 0.
Definition f_add := F 1 0.
Definition f_multiply := F 1 1.

Definition x1 := Tvar (X 1).
Definition x2 := Tvar (X 2).
Definition x3 := Tvar (X 3).

Definition Ic : Con-> bool := fun c =>
  match c with
  | C 0 => false
  | C 1 => true
  | _ => false
  end.

Definition If :=  
  fun f => 
  match f with
  | F 0 0 => fun v:vector bool (arity_F f) =>  
             match v with
             | vectorcons _  x 0 (vector0 _) => negb(x)
             | _ => true 
             end
  | F 1 0 => fun v:vector bool (arity_F f) =>  
             match v with
             | (vectorcons) _ x 1
                (vectorcons _ y 0 (vector0 _)) => orb x y
             | _ => true
             end
  | F 1 1 => fun v:vector bool (arity_F f) =>  
             match v with
             | (vectorcons) _ x 1
                (vectorcons _ y 0 (vector0 _)) => andb x y
             | _ => true
             end
  | _ => fun v:vector bool (arity_F f) =>  
             match v with
             |  _ => true
             end
  end. 

Definition Ir := fun r => 
  match r with 
  | _ => fun v:vector bool (arity_R r) =>  
             match v with
             | _ => True
             end 
  end.

Definition satisfy p:= satisfy_Formula bool Ic If Ir p.

(***************************************************)
(****************** 布尔代数的性质 ******************)
(***************************************************)


(************ 交换律 ************)

(* (F+(X1,X2) = F+(X2,X1)); *)
Definition vector1 := x1 :: x2 :: [].
Definition vector2 := x2 :: x1 :: [].
Notation "f+(x1,x2)" := (Tfun f_add vector1).
Notation "f+(x2,x1)" :=  (Tfun f_add vector2).
Theorem Commutative_law: satisfy f+(x1,x2) ≌ f+(x2,x1).
Proof.
  repeat red. intro. simpl. destruct (v(X 1)) eqn: E;
  destruct (v(X 2)) eqn: E'; auto.  
Qed.

(* (Fx (x1, x2) = Fx (x2, x1)) *)
Notation "fx(x1,x2)" := (Tfun f_multiply vector1).
Notation "fx(x2,x1)" := (Tfun f_multiply vector2).
Theorem Commutative_law': satisfy fx(x1,x2) ≌ fx(x2,x1).
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  destruct (v(X 2)) eqn: E'; auto.  
Qed.


(************* 结合律 *************)

(*  F+(F+(x1,x2),x3) = F+(x1,F+(x2,x3)) *)
Definition vector3 := x2 :: x3 :: []. 
Definition vector4 := x1 :: (Tfun f_add vector3) :: [].
Notation "F+(F+(x1,x2),x3)" := 
  (Tfun f_add ((Tfun f_add vector1) :: x3 :: [])).
Notation "F+(x1,F+(x2,x3)" := (Tfun f_add vector4).
Theorem Associative_law: satisfy F+(F+(x1,x2),x3) ≌ F+(x1,F+(x2,x3).
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  destruct (v(X 2)) eqn: E';destruct (v(X 3)) eqn: E'';  
  auto.  
Qed.

(* Fx(Fx(x1,x2),x3) = Fx(x1,Fx(x2,x3)) *)
Definition vector5 := (Tfun f_multiply vector1) :: x3 :: [].
Definition vector6 := x1 :: (Tfun f_multiply vector3) :: [].
Notation "Fx(Fx(x1,x2),x3)" := (Tfun f_multiply vector5).
Notation "Fx(x1,Fx(x2,x3))" := (Tfun f_multiply vector6).
Theorem Associative_law': satisfy Fx(Fx(x1,x2),x3) ≌ Fx(x1,Fx(x2,x3)).
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  destruct (v(X 2)) eqn: E'; destruct (v(X 3)) eqn: E'';
  auto.  
Qed.


(************* 恒等律 *************)

(* F+(x1,C0) = x1 *)
Definition vector7 := x1 :: c0 :: [].
Notation "F+(x1,C0)" := (Tfun f_add vector7).
Theorem Identity_law: satisfy F+(x1,C0) ≌ x1.
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  auto. 
Qed. 

(*  Fx(x1,C1) = x1 *)
Definition vector8 := x1 :: c1 :: [].
Notation "Fx(x1,C1)" := (Tfun f_multiply vector8).
Theorem Identity_law': satisfy Fx(x1,C1) ≌ x1.
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  auto.     
Qed.


(************* 空单元 *************)

(* Fx(x1,C0) = C0 *)
Notation "Fx(x1,C0)" := (Tfun f_multiply vector7).
Theorem Constant_law: satisfy Fx(x1,C0) ≌ c0.
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  auto.     
Qed.

(*  F+(x1,C1) = C1; *)
Notation "F+(x1,C1)" := (Tfun f_add vector8).
Theorem Constant_law': satisfy (Tfun f_add vector8) ≌ c1.
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  auto.    
Qed.


(************* 分配律 *************)

(* Fx(x1,F+(x2,x3)) = F+(Fx(x1,x2),Fx(x1,x3)) *)
Definition vector9 := x1 :: x3 :: [].
Definition vector10 := x1 :: (Tfun f_add vector3) :: [].
Definition vector10' := 
  (Tfun f_multiply vector1) :: (Tfun f_multiply vector9) :: [].
Notation "Fx(x1,F+(x2,x3))" := (Tfun f_multiply vector10).
Notation "F+(Fx(x1,x2),Fx(x1,x3))" := (Tfun f_add vector10').
Theorem Distributive_law: satisfy Fx(x1,F+(x2,x3)) ≌ 
  F+(Fx(x1,x2),Fx(x1,x3)).
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  destruct (v(X 2)) eqn: E'; destruct (v(X 3)) eqn: E'';
  auto.   
Qed.

(* F+(x1,Fx(x2,x3)) = Fx(F+(x1,x2),F+(x1,x3)) *)
Definition vector11 := x1 :: (Tfun f_multiply vector3) :: [].
Definition vector11' := 
  (Tfun f_add vector1) :: (Tfun f_add vector9) :: [].
Notation "F+(x1,Fx(x2,x3))" := (Tfun f_add vector11).
Notation "Fx(F+(x1,x2),F+(x1,x3))" := (Tfun f_multiply vector11').
Theorem Distributive_law': satisfy F+(x1,Fx(x2,x3)) ≌ 
  Fx(F+(x1,x2),F+(x1,x3)).
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  destruct (v(X 2)) eqn: E'; destruct (v(X 3)) eqn: E'';
  auto.   
Qed.


(************* 互补 *************)

(*  F+(x1,Fs(x1)) = C1 *)
Definition vector12 := x1 :: (Tfun fs (x1 :: [])) :: [].
Notation "F+(x1,Fs(x1))" := (Tfun f_add vector12).
Theorem Complementation_law: satisfy F+(x1,Fs(x1)) ≌ c1.
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  auto.    
Qed.

(* Fx(x1,Fs(x1) = C0 *)
Notation "Fx(x1,Fs(x1))" := (Tfun f_multiply vector12).
Theorem Complementation_law': satisfy Fx(x1,Fs(x1)) ≌ c0.
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  auto.    
Qed.


(************* 互斥 **************)

(* ¬ (c0 = c1) *)
Theorem Exclusive_law: satisfy ¬ (c0 ≌ c1).
Proof.
  repeat red. simpl. intros. inversion H.   
Qed.


(************* 吸收律 *************)

(*  F+(x1,Fx(x1,x2)) = x1*)
Definition vector13 := x1 :: (Tfun f_multiply vector1) :: [].
Notation "F+(x1,Fx(x1,x2))" := (Tfun f_add vector13).
Theorem Absorption_law: satisfy F+(x1,Fx(x1,x2)) ≌ x1. 
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  destruct (v(X 2)) eqn: E'; auto.   
Qed.

(*  Fx(x1,F+(x1,x2)) = x1*)
Definition vector13' := x1 :: (Tfun f_add vector1) :: [].
Notation "Fx(x1,F+(x1,x2))" := (Tfun f_multiply vector13').
Theorem Absorption_law': satisfy Fx(x1,F+(x1,x2)) ≌ x1.
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  destruct (v(X 2)) eqn: E'; auto.
Qed.


(************* 自反律 *************)

(* Fs(Fs(x1)) = x1  *)
Notation "Fs(Fs(x1))" := (Tfun fs ((Tfun fs (x1 :: [])) ::[])).
Theorem Reflexivity_law: satisfy Fs(Fs(x1)) ≌ x1.
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E; 
  auto.   
Qed.


(************* 摩根定理 *************)

(* Fs(F+(x1,x2)) = Fx(Fs(x1),Fs(x2))  *)
Definition vector14 := (Tfun fs (x1 :: []) :: (Tfun fs (x2 :: [])) :: []).
Notation "Fs(F+(x1,x2))" := (Tfun fs (Tfun f_add (vector1) :: [])).
Notation "Fx(Fs(x1),Fs(x2))" := (Tfun f_multiply vector14).
Theorem Morgan_law: satisfy Fs(F+(x1,x2)) ≌ Fx(Fs(x1),Fs(x2)).
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  destruct (v(X 2)) eqn: E'; auto.
Qed.

(* Fs(Fx(x1,x2)) = F+(Fs(x1),Fs(x2)) *)
Notation "Fs(Fx(x1,x2))" := (Tfun fs (Tfun f_multiply (vector1) :: [])).
Notation "F+(Fs(x1),Fs(x2))" := (Tfun f_add vector14).
Theorem Morgan_law': satisfy Fs(Fx(x1,x2)) ≌ F+(Fs(x1),Fs(x2)).
Proof.
  repeat red. simpl. intro. destruct (v(X 1)) eqn: E;
  destruct (v(X 2)) eqn: E'; auto.   
Qed.
