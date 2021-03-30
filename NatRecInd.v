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

Proof. 
  intros a b c. 
  induction c. 
  simpl. 
  reflexivity. 
  simpl. 
  rewrite -> IHc. 
  reflexivity. 
Qed.  

(*PROOF THAT Sa + b = a + Sb*)
Theorem sucessor: forall (a b: Nat),(S a) + b = a + (S b).

Proof. 
  intros a b.  
  induction b. 
  simpl. 
  reflexivity. 
  simpl. 
  rewrite -> IHb. 
  simpl. 
  reflexivity. 
  Qed.

(*PROOF THAT a+0 = 0+a*)
Theorem plus_O: forall (a: Nat), a = O + a.

Proof. 
  intro a.
  induction a.
  simpl. 
  reflexivity.
  simpl.
  rewrite <- IHa.
  reflexivity.
Qed.

(*PROOF THAT PLUS IS COMMUTATIVE*)
Theorem plusCommutative: forall (a b: Nat), a + b = b + a.

Proof. 
  intros a b.
  induction a.
    -simpl.
     rewrite plus_O.
     reflexivity.
    -simpl.
     rewrite <- IHa.
     rewrite -> sucessor.
     simpl.
     reflexivity.
Qed.

(*EXERCÍCIO x4.16 FMCBOOK (Distributividade Multiplicação)*)
Theorem multDistributivity: forall (x y z: Nat), x*(y+z) = (x*y) + (x*z).

Proof.
  intros x y z.
  induction z.
    trivial.
    simpl.
    rewrite IHz.
    rewrite plusCommutative.
    rewrite plusAssociative.
    assert(T: x * z + x = x + x * z).
      -rewrite plusCommutative.
       reflexivity.
      -rewrite T.
       reflexivity.
Qed.

(*EXERCÍCIO x4.14 FMCBOOK (Associatividade Multiplicação)*)
Theorem multAssociative: forall(x y z: Nat), (x*y)*z = x*(y*z).

Proof.
  intros x y z.
  induction z.
    -simpl.
     reflexivity.
    -simpl.
     rewrite multDistributivity.
     rewrite IHz.
     reflexivity.
Qed.

Lemma mult_n_0: forall(n:Nat),O*n = O.

Proof.
  intro n.
  induction n.
    -simpl.
     reflexivity.
    -simpl.
     rewrite IHn.
     simpl.
     reflexivity.
Qed.

Lemma plus_n_0: forall(n:Nat), O+n = n.

Proof.
  intro n.
  induction n.
    -simpl.
     reflexivity.
    -simpl.
     rewrite IHn.
     reflexivity.
Qed.

Lemma mult_n_Sm : forall (n m : Nat), n * S m = n + n * m.

Proof.
  intros n m.
  induction n.
    -reflexivity.
    -simpl.
     reflexivity.
Qed.

Lemma plus_1_l : forall (n:Nat), (S O) + n = S n.
  intros n.
  induction n.
    -simpl.
     reflexivity.
    -simpl.
     rewrite IHn.
     reflexivity.
Qed.

Theorem multCommutative : forall (n m : Nat), n * m = m * n.

Proof.
  induction n.
    -induction m.
      +simpl.
       reflexivity.
      +simpl. 
       rewrite IHm.
       simpl.
       reflexivity.
    -induction m.
      +simpl.
       rewrite mult_n_0.
       simpl.
       reflexivity.
      +simpl.
       rewrite IHm.
       rewrite <- (IHn (S m)).
       simpl.
       rewrite <- (IHn m).
       rewrite <-(plusAssociative (S n)m(n*m)).
       rewrite <-(plusAssociative (S m)n(n*m)).
       rewrite <- plus_1_l.
       rewrite <-(plus_1_l m).
       rewrite (plusAssociative (S O)(n)(m)).
       rewrite (plusCommutative n m).
       rewrite <- (plusAssociative (S O) m n).
       reflexivity.
Qed.
