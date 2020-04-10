Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint addn (n1 n2 : nat) :=
  match n1 with
  | O => n2
  | S n1' => S (addn n1' n2)
  end.

Fixpoint muln (n1 n2 : nat) :=
  match n1 with
  | O => O
  | S n1' => addn n2 (muln n1' n2)
  end.

Lemma addn_n_O : forall (n : nat), addn n O = n.
  induction n.
    reflexivity.

    simpl.
    rewrite IHn.
    reflexivity.
  Defined.

Lemma addn_Scomm : forall (n1 n2 : nat), addn (S n1) n2 = addn n1 (S n2).
  induction n1.
    intro n2.
    reflexivity.

    intro n2.
    simpl.
    rewrite <- IHn1.
    reflexivity.
  Defined.

Theorem addn_comm : forall (n1 n2 : nat), addn n1 n2 = addn n2 n1.
  induction n1.
    intro n2.
    rewrite addn_n_O.
    reflexivity.

    intro n2.
    rewrite <- addn_Scomm.
    simpl.
    rewrite IHn1.
    reflexivity.
  Defined.

Theorem addn_assoc : forall (n1 n2 n3 : nat), addn (addn n1 n2) n3 = addn n1 (addn n2 n3).
  induction n1.
    reflexivity.
    
    simpl.
    intros n2 n3.
    rewrite IHn1.
    reflexivity.
  Defined.

Lemma addn_n_mu_comm : forall (n1 n2 n3 : nat), addn n1 (addn n2 n3) = addn n2 (addn n1 n3).
  intros n1 n2 n3.
  rewrite <- addn_assoc.
  rewrite <- addn_assoc.
  rewrite (addn_comm n1 n2).
  reflexivity.
  Defined.

Lemma muln_n_Sm : forall (n1 n2 : nat), muln n1 (S n2) = addn n1 (muln n1 n2).
  induction n1.
    intro n2.
    reflexivity.

    intro n2.
    simpl.
    rewrite IHn1.
    rewrite addn_n_mu_comm.
    reflexivity.
  Defined.

Lemma muln_n_O : forall (n : nat), muln n O = O.
  induction n.
    reflexivity.

    simpl.
    assumption.
  Defined.

Theorem muln_comm : forall (n1 n2 : nat), muln n1 n2 = muln n2 n1.
  induction n1.
    intro n2.
    simpl.
    rewrite muln_n_O.
    reflexivity.

    intro n2.
    simpl.
    rewrite IHn1.
    rewrite muln_n_Sm.
    reflexivity.
  Defined.

Lemma addn_mdisthelp : forall (n1 n2 n3 n4 : nat), addn (addn n1 n2) (addn n3 n4) = addn (addn n1 n3) (addn n2 n4).
  intros n1 n2 n3 n4.
  rewrite (addn_assoc n1 n2 (addn n3 n4)).
  rewrite (addn_assoc n1 n3 (addn n2 n4)).
  rewrite <- (addn_assoc n3 n2 n4).
  rewrite (addn_comm n3 n2).
  rewrite -> (addn_assoc n2 n3 n4).
  reflexivity.
  Defined.

Theorem muln_dist_addn : forall (n1 n2 n3 : nat), muln n1 (addn n2 n3) = addn (muln n1 n2) (muln n1 n3).
  induction n1.
    reflexivity.

    simpl.
    intros n2 n3.
    rewrite IHn1.
    rewrite (addn_mdisthelp n2 n3 (muln n1 n2) (muln n1 n3)).
    reflexivity.
  Defined.

Theorem muln_ldist : forall (n1 n2 n3 : nat), muln (addn n1 n2) n3 = addn (muln n1 n3) (muln n2 n3).
  intros n1 n2 n3.
  rewrite muln_comm.
  rewrite (muln_comm n1 n3).
  rewrite (muln_comm n2 n3).
  rewrite (muln_dist_addn n3 n1 n2).
  reflexivity.
  Defined.

Theorem muln_assoc : forall (n1 n2 n3 : nat), muln (muln n1 n2) n3 = muln n1 (muln n2 n3).
  induction n1.
    simpl. 
    reflexivity.
    
    simpl.
    intros n2 n3.
    rewrite muln_ldist.
    rewrite <- IHn1.
    reflexivity.
  Defined.

Inductive int : Set :=
  | P : nat -> int
  | N : nat -> int.

Check nat_ind.

Fixpoint red0 (i : int) :=
  match i with
  | P O => P O
  | P (S n) => P n
  | N O => N O
  | N (S n) => N n
  end.

Axiom pz_equals_nz : P O = N O.

Fixpoint c_nat_int (n : nat) : int :=
  P n.

Fixpoint neg (i : int) :=
  match i with
  | P O => P O
  | P n => N n
  | N n => P n
  end.

Fixpoint inci (i : int) :=
  match i with
  | P n => P (S n)
  | N O => P (S O)
  | N (S n) => N n
  end.

Fixpoint deci (i : int) :=
  match i with
  | P O => N (S O)
  | P (S n) => P n
  | N n => N (S n)
  end.

Fixpoint sub_PPn (n1 n2 : nat) :=
  match n1 with
  | O => N n2
  | S n1' => 
    match n2 with
    | O => P n1
    | S n2' => sub_PPn n1' n2'
    end
  end.

Lemma subPPn_O : forall n : nat, sub_PPn n O = P n.
  induction n.
    simpl.
    rewrite pz_equals_nz.
    reflexivity.

    reflexivity.
  Defined.

Fixpoint sub_PNn (n1 n2 : nat) :=
  match n1 with
  | O => P n2
  | S n1' => inci (sub_PNn n1' n2)
  end.

Lemma ps_eq_inc_P : forall n : nat, P (S n) = inci (P n).
  destruct n.
    reflexivity.

    reflexivity.
  Defined.

Lemma subPNn_O : forall n : nat, sub_PNn n O = P n.
  induction n.
    reflexivity.

    simpl.
    rewrite IHn.
    rewrite ps_eq_inc_P.
    reflexivity.
  Defined.

Lemma subPN_eq_Padd : forall n1 n2 : nat, sub_PNn n1 n2 = P (addn n1 n2).
  induction n1.
    reflexivity.

    simpl.
    intros n2.
    rewrite (ps_eq_inc_P (addn n1 n2)).
    rewrite IHn1.
    reflexivity.
  Defined.

Fixpoint sub_NPn (n1 n2 : nat) :=
  match n1 with
  | O => N n2
  | S n1' => deci (sub_NPn n1' n2)
  end.

Lemma ns_eq_dec_N : forall n : nat, N (S n) = deci (N n).
  destruct n.
    reflexivity.
    
    reflexivity.
  Defined.

Lemma subNPn_O : forall n : nat, sub_NPn n O = N n.
  induction n.
    reflexivity.
    
    simpl.
    rewrite IHn.
    rewrite ns_eq_dec_N.
    reflexivity.
  Defined.

Lemma subNP_eq_Nadd : forall n1 n2 : nat, sub_NPn n1 n2 = N (addn n1 n2).
  induction n1.
    reflexivity.

    simpl.
    intros n2.
    rewrite (ns_eq_dec_N (addn n1 n2)).
    rewrite IHn1.
    reflexivity.
  Defined.


Fixpoint sub_NNn (n1 n2 : nat) :=
  match n1 with
  | O => P n2
  | S n1' =>
    match n2 with
    | O => N n1
    | S n2' => sub_NNn n1' n2'
    end
  end.

Lemma subNNn_O : forall n : nat, sub_NNn n O = N n.
  induction n.
    simpl.
    rewrite pz_equals_nz.
    reflexivity.

    reflexivity.
  Defined.

Fixpoint subi (i1 i2 : int) :=
  match i1, i2 with
  | P n1, P n2 => sub_PPn n1 n2
  | P n1, N n2 => sub_PNn n1 n2
  | N n1, P n2 => sub_NPn n1 n2
  | N n1, N n2 => sub_NNn n1 n2
  end.

Fixpoint addi (i1 i2 : int) :=
  match i1, i2 with
  | P n1, P n2 => sub_PNn n1 n2
  | P n1, N n2 => sub_PPn n1 n2
  | N n1, P n2 => sub_NNn n1 n2
  | N n1, N n2 => sub_NPn n1 n2
  end.

Theorem pos_add_ntoi : forall n1 n2 : nat, P (addn n1 n2) = addi (P n1) (P n2).
  induction n1.
    reflexivity.

    intro n2.
    simpl.
    rewrite ps_eq_inc_P.
    rewrite subPN_eq_Padd.
    reflexivity.
  Defined.

Theorem neg_add_ntoi : forall n1 n2 : nat, N (addn n1 n2) = addi (N n1) (N n2).
  induction n1.
    reflexivity.

    intro n2.
    simpl.
    rewrite ns_eq_dec_N.
    rewrite subNP_eq_Nadd.
    reflexivity.
  Defined.

Theorem addi_O_i : forall i : int, addi (P O) i = i.
  induction i.
    reflexivity.
    reflexivity.
  Defined.

Theorem addi_i_O : forall i : int, addi i (P O) = i.
  induction i.
    simpl.
    rewrite subPNn_O.
    reflexivity.
    
    simpl.
    rewrite subNNn_O.
    reflexivity.
  Defined.

