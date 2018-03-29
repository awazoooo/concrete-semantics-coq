(* Concrete Semantics with Isabelle/HOLに出てくるプログラムをCoqで実装 *)

Section Chapter3.
  (* 主にIMPという言語についてのお話 *)
  (* 正直 い つ も の *)
  Require Import String.
  Open Scope string.
  
  Definition vname := string.
  Inductive aexp := 
    | N : forall n: nat, aexp (* 原文はint *)
    | V : forall s: vname, aexp (* 変数 *)
    | Plus : forall l r: aexp, aexp. (* 加算 *)

  Definition val := nat.
  Definition state := vname -> val. (* コンテキスト *)

  Fixpoint aval (e: aexp) (s: state) : val :=
    match e with
    | N n => n
    | V x => s x
    | Plus l r => aval l s + aval r s
    end.

  Compute aval (Plus (N 3) (V "x")) (fun _ => 5).

  (* 定数同士のPlusのときに簡単にする最適化 *)
  Fixpoint asimp_const (e: aexp) : aexp :=
    match e with
    | N n => N n
    | V x => V x
    | Plus l r =>
      match (asimp_const l, asimp_const r) with
      | (N n0, N n1) => N (n0 + n1)
      | (e0, e1) => Plus e0 e1
      end
    end.

  Compute asimp_const (Plus (V "x") (Plus (N 3) (N 1))).

  (* asimp_constがaexpの意味を変えないことの証明 *)
  Lemma aval_asimp_const : forall (e: aexp) (s: state), aval (asimp_const e) s = aval e s.
  Proof.
    induction e; intros; simpl.
    - reflexivity.
    - reflexivity.
    - specialize (IHe1 s); specialize (IHe2 s).
      rewrite <- IHe1; rewrite <- IHe2.
      destruct (asimp_const e1); destruct (asimp_const e2); simpl; try reflexivity.
  Qed.      

  (* asimp_constをより最適化 *)
  Definition plus (l r: aexp) : aexp :=
    match (l, r) with
    | (N n0, N n1) => N (n0 + n1)
    | (N n, e) => if Nat.eqb n 0 then e else Plus (N n) e
    | (e, N n) => if Nat.eqb n 0 then e else Plus e (N n)
    | (e0, e1) => Plus e0 e1
    end.

  (* aval_asimpと同じ感じ *)
  Lemma aval_plus : 
    forall (e0 e1: aexp) (s: state), aval (plus e0 e1) s = aval e0 s + aval e1 s.
  Proof.
    SearchPattern (_ = _ + 0).
    induction e0; induction e1; intros; simpl; try reflexivity;
    destruct n; simpl; try apply plus_n_O; try reflexivity.
  Qed.

  (* Plusをplusに置き換え *)
  Fixpoint asimp (e: aexp) : aexp :=
    match e with
    | N n => N n
    | V x => V x
    | Plus e0 e1 => plus (asimp e0) (asimp e1)
    end.

  (* avalのあれ *)
  Lemma aval_asimp : forall (e: aexp) (s: state), aval (asimp e) s = aval e s.
  Proof.
    induction e; intros; simpl; try reflexivity.
    specialize (IHe1 s); specialize (IHe2 s).
    rewrite <- IHe1; rewrite <- IHe2.
    apply aval_plus.
  Qed.

  (* Ex 3.1 *)
  Definition optimal (e: aexp) : Prop :=
    match e with
    | Plus e0 e1 =>
      match (e0, e1) with
      | (N _, N _) => False
      | _ => True
      end
    | _ => True
    end.

  Lemma asimp_const_optimal: forall (e: aexp), optimal (asimp_const e).
  Proof.
    induction e; intros; simpl; try apply I.
    destruct (asimp_const e1); destruct (asimp_const e2); simpl; apply I.
  Qed.

  (* Ex 3.2 *)
  Fixpoint full_asimp (e: aexp) : aexp :=
    match e with
    | N n => N n
    | V x => V x
    | Plus e0 e1 => 
      match (full_asimp e0, full_asimp e1) with
      | (N n0, N n1) => N (n0 + n1)
      | (N n, Plus n0 n1) => 
        match (n0, n1) with
        | (N n', _) => Plus (N (n + n')) n1
        | (_, N n') => Plus n0 (N (n + n'))
        | (_, _) => Plus e0 e1
        end
      | (Plus n0 n1, N n) =>
        match (n0, n1) with
        | (N n', _) => Plus (N (n + n')) n1
        | (_, N n') => Plus n0 (N (n + n'))
        | (_, _) => Plus e0 e1
        end
      | (Plus n0 n1, Plus n2 n3) =>
        match (n0, n1, n2, n3) with
        | (N n0', _, N n2', _) => Plus (N (n0' + n2')) (Plus n1 n3)
        | (N n0', _, _, N n3') => Plus (N (n0' + n3')) (Plus n1 n2)
        | (_, N n1', N n2', _) => Plus (N (n1' + n2')) (Plus n0 n3)
        | (_, N n1', _, N n3') => Plus (N (n1' + n3')) (Plus n0 n2)
        | _ => Plus e0 e1
        end
      | (_, _) => Plus e0 e1 (* どっちかにVがあるとどうしようもない *)
      end
    end.

  Compute full_asimp (Plus (N 1) (Plus (V "x") (N 2))).

  Require Import Lia.
  
  Fact add_shuffle_4 : forall a b c d: nat, a + b + (c + d) = c + (a + b + d).
  Proof.
    intros; lia.
  Qed.    

  Create HintDb chapter3.
  Hint Resolve add_shuffle_4 : chapter3.
  SearchPattern(_ + (_ + _) = _ + (_ + _)).

  Lemma aval_full_asimp : 
    forall (e: aexp) (s: state), aval (full_asimp e) s = aval e s.
  Proof.
    induction e; intros; simpl; try reflexivity.
    specialize (IHe1 s); specialize (IHe2 s).
    rewrite <- IHe1; rewrite <- IHe2.
    destruct (full_asimp e1); destruct (full_asimp e2); simpl; try reflexivity;
      try rewrite <- IHe1; try rewrite <- IHe2; simpl; try reflexivity.
    destruct a1; destruct a2; simpl; intuition.
    Focus 2.
  Admitted. (* とてつもなくめんどくさそうなので保留 *)

  Compute (string_dec "hoge" "hoge").

  Fixpoint subst' (s: vname) (e0 e1: aexp) : aexp :=
    match e1 with
    | N n => N n
    | V x => 
      match string_dec s x with
      | left _ => e0
      | right _ => (V x)
      end
    | Plus n0 n1 => Plus (subst' s e0 n0) (subst' s e0 n1)
    end.

  Compute subst' "x" (N 3) (Plus (V "x") (V "y")).

  Lemma subst'_lemma: forall (e0 e1 elm: aexp) (x: vname) (s: state), 
      aval e0 s = aval e1 s -> aval (subst' x elm e0) s = aval (subst' x elm e1) s.
  Proof.
    intros.
    induction e0; induction e1.
    simpl in *. assumption.
    simpl. 
    repeat match goal with
    | [ |- context[if ?P then _ else _]] => destruct P; simpl; try assumption
    end.
  Admitted.

  (* 証明ムズイ *)

  (* 3.2 *)

  Require Import Bool.

  Inductive bexp := 
  | Bc : forall b: bool, bexp
  | Not : forall b: bexp, bexp
  | And : forall b0 b1: bexp, bexp
  | Less : forall a0 a1: aexp, bexp.

  Fixpoint bval (b: bexp) (s: state) : bool :=
    match b with
    | Bc v => v
    | Not b' => negb (bval b' s)
    | And b0 b1 => andb (bval b0 s) (bval b1 s)
    | Less a0 a1 => Nat.leb (aval a0 s) (aval a1 s)
    end.

  Definition not (b: bexp) : bexp :=
    match b with
    | Bc true => Bc false
    | Bc false => Bc true
    | _ => Not b
    end.

  Definition and (b0 b1: bexp) : bexp :=
    match (b0, b1) with
    | (Bc true, b1') => b1'
    | (b0', Bc true) => b0'
    | (Bc false, _) => Bc false
    | (_, Bc false) => Bc false
    | (_, _) => And b0 b1
    end.

  Definition less (a0 a1: aexp) : bexp :=
    match (a0, a1) with
    | (N n0, N n1) => Bc (Nat.leb n0 n1)
    | (_, _) => Less a0 a1
    end.

  Fixpoint bsimp (b: bexp) : bexp :=
    match b with
    | Bc v => Bc v
    | Not b' => not (bsimp b')
    | And b0 b1 => and (bsimp b0) (bsimp b1)
    | Less a0 a1 => less (asimp a0) (asimp a1)
    end.

  (* 演習は省略 *)
  
  (* 3.3 *)
  Inductive instr :=
  | LOADI : forall (n: val), instr
  | LOAD  : forall (s: vname), instr
  | ADD : instr.

  Require Import List.
  
  Definition stack := list nat.

  Definition hd2 (l: list nat) := List.hd 0 (List.tl l).

  Definition tl2 (l: list nat) := List.tl (List.tl l).

  Definition exec1 (i: instr) (s: state) (stk: stack) : stack :=
    match i with
    | LOADI n => n :: stk
    | LOAD  x => (s x) :: stk
    | Add => (hd2 stk + hd 0 stk) :: tl2 stk
    end.

  (* headはデフォルト引数が必要だったらしい *)