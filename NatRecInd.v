Inductive Nat : Type :=
  | O
  | S (n : Nat).

Fixpoint plus (n : Nat) (m : Nat) : Nat :=
  match m with
    | O => n
    | S m' => S (plus n m')
  end.
  
  Notation "x + y" := (plus x y).
  
(*EXERCÍCIO x4.3 FMCBOOK*)
Compute (plus O (S (S (S (S O))))).

(*EXERCÍCIO X4.4 FMCBOOK* usando notation*)
Compute S (S (S O)) + (S(S O)+S O).
Compute (S (S (S O)) + S (S O)) + S O.

(*EXERCÍCIO X4.5 FMCBOOK*)
Fixpoint d (n:Nat): Nat :=
  match n with
  | O => O
  | S n' => S (S (d n'))
  end.
Compute (d (S (S (S O)))).

(*EXERCÍCIO X4.6 FMCBOOK -> Definindo Multiplicação*)
Fixpoint mult (n: Nat) (m:Nat) :Nat :=
  match m with
  | O => O
  | S m => n + (mult n m)
  end.
 Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
                       
(*EXERCÍCIO X4.7 FMCBOOK*)                  
Compute (S (S O)*(O + S O)).

(*EXERCÍCIO X4.8 FMCBOOK*)
Compute (S (S O) * S (S (S O))).
Compute (S (S (S O)) * S (S O)).

(*EXERCÍCIO X4.9 FMCBOOK -> Definindo a Exponenciação*)
Fixpoint expo (n: Nat) (m: Nat) :Nat :=
  match m with
  |O => S O
  |S m' => (expo n m')*n
  end.
Notation "x ^ y" := (expo x y).

(*EXERCÍCIO X4.10 FMCBOOK*)
Compute S (S O) ^ S (S (S O)).

(*EXERCÍCIO X4.11 FMCBOOK*)
Fixpoint fibo (n: Nat) :Nat :=
  match n with
  |O => O
  |S n' => match n' with
           | O => S O
           | S n'' => fibo n' + fibo n''
           end
  end.

(*PROOF THAT PLUS IS ASSOCIATIVE*)
Theorem plusAssociative: forall (a b c: Nat), (a+b)+c = a+(b+c).

Proof. intros a b c. induction c. simpl. reflexivity. simpl. rewrite -> IHc. reflexivity. Qed.  

(*PROOF THAT Sa + b = a + Sb*)
Theorem sucessor: forall (a b: Nat),(S a) + b = a + S b.

Proof. intros a b. induction b. simpl. reflexivity. simpl. rewrite -> IHb. simpl. reflexivity. Qed.
