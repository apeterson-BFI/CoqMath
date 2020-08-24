Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint addn (n1 n2 : nat) :=
  match n1 with
  | O => n2
  | S n1' => S (addn n1' n2)
  end.

Lemma addn_O_m : forall (m : nat), addn O m = m.
  reflexivity.
  Defined.

Lemma addn_n_O : forall (n : nat), addn n O = n.
  induction n; try reflexivity.
  simpl; rewrite IHn; reflexivity.
  Defined.

Lemma addn_Sn_m : forall (n m : nat), addn (S n) m = S (addn n m).
  reflexivity.
  Defined.

Lemma addn_n_Sm : forall (n m : nat), addn n (S m) = S (addn n m).
  induction n; try reflexivity.
  intros m. rewrite ?addn_Sn_m.
  rewrite IHn. reflexivity.
  Defined.

Lemma addn_S_comm : forall (n m : nat), addn n (S m) = addn (S n) m.
  intros n m.
  rewrite addn_Sn_m. rewrite addn_n_Sm. 
  reflexivity. Defined.

Theorem addn_comm : forall (n m : nat), addn n m = addn m n.
  induction n.
  simpl. intros m. rewrite addn_n_O. reflexivity.
  intros m. rewrite addn_Sn_m. rewrite addn_n_Sm.
  rewrite IHn. reflexivity.
  Defined.

Theorem addn_assoc : forall (n m o : nat), addn (addn n m) o = addn n (addn m o).
  induction n; destruct m; destruct o; 
  try reflexivity;
  try (rewrite ?addn_n_O; rewrite ?addn_O_n; reflexivity).
  rewrite ?addn_Sn_m. rewrite ?addn_n_Sm. rewrite addn_Sn_m.
  rewrite IHn. reflexivity.
  Defined.

Fixpoint muln (n1 n2 : nat) :=
  match n1 with
  | O => O
  | S n1' => addn n2 (muln n1' n2)
  end.

Lemma muln_n_O : forall (n : nat), muln n O = O.
  induction n; try reflexivity.
  simpl.
  assumption.
  Defined.

Lemma muln_O_m : forall (m : nat), muln O m = O.
  reflexivity.
  Defined.

Lemma muln_Sn_m : forall (n m : nat), muln (S n) m = addn m (muln n m).
  reflexivity.
  Defined.

Lemma muln_n_Sm : forall (n m : nat), muln n (S m) = addn n (muln n m).
  induction n; try reflexivity.
  intros m. simpl.
  rewrite IHn.
  rewrite <- ?addn_assoc.
  rewrite (addn_comm m n).
  reflexivity.
  Defined.

Theorem muln_comm : forall (n m : nat), muln n m = muln m n.
  induction n; destruct m; try reflexivity;
  try (rewrite ?muln_n_O; rewrite ?muln_O_m; reflexivity).
  rewrite ?muln_Sn_m. rewrite ?muln_n_Sm.
  rewrite ?addn_Sn_m. rewrite IHn.
  rewrite <- ?addn_assoc. rewrite (addn_comm m n). reflexivity.
  Defined.

Lemma addn_addn_nm_no : forall (n m o : nat), addn n (addn n (addn m o)) = addn (addn n m) (addn n o).
  intros n m o.
  rewrite addn_assoc.
  rewrite <- (addn_assoc m n o).
  rewrite (addn_comm m n).
  rewrite addn_assoc.
  reflexivity.
  Defined.

Theorem muln_addn : forall (n m o : nat), muln (addn n m) o = addn (muln n o) (muln m o).
  induction n; destruct m; destruct o; try reflexivity;
  try (rewrite ?muln_n_O; rewrite ?muln_O_m; reflexivity).
  rewrite ?muln_O_m. rewrite ?addn_n_O. reflexivity.
  rewrite addn_Sn_m. rewrite addn_n_Sm.
  rewrite muln_Sn_m. rewrite muln_Sn_m.
  rewrite IHn.
  rewrite ?muln_Sn_m.
  rewrite addn_addn_nm_no.
  reflexivity.
  Defined.

Lemma muln_addn_r : forall (n m o : nat), muln n (addn m o) = addn (muln n m) (muln n o).
  intros n m o.
  rewrite muln_comm.
  rewrite muln_addn.
  rewrite (muln_comm m n). rewrite (muln_comm o n).
  reflexivity.
  Defined.

Theorem muln_assoc : forall (n m o : nat), muln (muln n m) o = muln n (muln m o).
  induction n.
  reflexivity.
  simpl. intros m o.
  rewrite ?muln_addn_r. rewrite muln_addn.
  rewrite IHn.
  reflexivity.
  Defined.

Inductive int : Set :=
  | P : nat -> int
  | N : nat -> int.

Axiom pz_equals_nz : P O = N O.

Fixpoint neg (i : int) :=
  match i with
  | P O => P O
  | P n => N n
  | N n => P n
  end.

Lemma neg_Pn : forall (n : nat), neg (P n) = N n.
  destruct n; try reflexivity. 
  rewrite <- pz_equals_nz.
  reflexivity.
  Defined.

Lemma neg_Nn : forall (n : nat), neg (N n) = P n.
  reflexivity.
  Defined.

Lemma neg_neg : forall (i : int), neg (neg i) = i.
  destruct i; destruct n; try (rewrite <- pz_equals_nz); reflexivity.
  Defined.

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

Lemma inci_Pn : forall (n : nat), inci (P n) = P (S n).
  reflexivity.
  Defined.

Lemma inci_NSn : forall (n : nat), inci (N (S n)) = N n.
  reflexivity.
  Defined.

Lemma deci_PSn : forall (n : nat), deci (P (S n)) = P n.
  reflexivity.
  Defined.

Lemma deci_Nn : forall (n : nat), deci (N n) = N (S n).
  reflexivity.
  Defined.

Lemma neg_inci : forall (i : int), neg (inci i) = deci (neg i).
  destruct i; destruct n; try reflexivity.
  Defined.

Lemma neg_deci : forall (i : int), neg (deci i) = inci (neg i).
  destruct i; destruct n; try reflexivity.
  rewrite deci_PSn.
  rewrite ?neg_Pn.
  rewrite inci_NSn.
  reflexivity.
  Defined.

Lemma inci_deci : forall (i : int), inci (deci i) = i.
  destruct i; induction n; try reflexivity.
  simpl. rewrite pz_equals_nz. reflexivity.
  Defined.

Lemma deci_inci : forall (i : int), deci (inci i) = i.
  destruct i; induction n; try reflexivity.
  simpl. rewrite pz_equals_nz. reflexivity.
  Defined.

Fixpoint sub_PPn (n1 n2 : nat) :=
  match n1 with
  | O => N n2
  | S n1' => 
    match n2 with
    | O => P n1
    | S n2' => sub_PPn n1' n2'
    end
  end.

Lemma subPPn_O_m : forall (m : nat), sub_PPn O m = N m.
  reflexivity.
  Defined.

Lemma subPPn_n_O : forall (n : nat), sub_PPn n O = P n.
  destruct n.
  simpl. rewrite pz_equals_nz; reflexivity.
  reflexivity.
  Defined.

Lemma subPPn_Sn_Sm : forall (n m : nat), sub_PPn (S n) (S m) = sub_PPn n m.
  reflexivity.
  Defined.

Lemma subPPn_n_n : forall (n : nat), sub_PPn n n = P O.
  induction n.
  simpl; rewrite ?pz_equals_nz; try reflexivity.
  simpl. assumption.
  Defined.

Lemma subPPn_Sn_m : forall (n m : nat), sub_PPn (S n) m = inci (sub_PPn n m).
  induction n.
  intros m.
  rewrite subPPn_O_m.
  destruct m; reflexivity.
  destruct m. rewrite ?subPPn_n_O.
  reflexivity.
  rewrite ?subPPn_Sn_Sm.
  rewrite IHn.
  reflexivity.
  Defined.

Lemma subPPn_n_Sm : forall (n m : nat), sub_PPn n (S m) = deci (sub_PPn n m).
  induction n.
  intros m.
  rewrite ?subPPn_O_m.
  destruct m; reflexivity.
  destruct m. rewrite ?subPPn_n_O.
  rewrite subPPn_Sn_Sm. rewrite subPPn_n_O.
  rewrite deci_PSn.
  reflexivity.
  rewrite ?subPPn_Sn_Sm.
  rewrite IHn. reflexivity.
  Defined.

Lemma subPPn_anticomm : forall (n m : nat), sub_PPn n m = neg (sub_PPn m n).
  induction n.
  intros m. 
  rewrite subPPn_n_O. rewrite subPPn_O_m.
  rewrite neg_Pn. reflexivity.
  intros m. 
  rewrite subPPn_Sn_m. rewrite subPPn_n_Sm.
  rewrite neg_deci.
  rewrite IHn.
  reflexivity.
  Defined.

Fixpoint sub_PNn (n1 n2 : nat) :=
  match n1 with
  | O => P n2
  | S n1' => inci (sub_PNn n1' n2)
  end.

Lemma subPNn_n_O : forall (n : nat), sub_PNn n O = P n.
  induction n; try reflexivity.
  simpl. rewrite IHn.
  rewrite inci_Pn.
  reflexivity.
  Defined.

Lemma subPNn_O_m : forall (m : nat), sub_PNn O m = P m.
  reflexivity.
  Defined.

Lemma subPNn_Sn_m : forall (n m : nat), sub_PNn (S n) m = inci (sub_PNn n m).
  reflexivity.
  Defined.

Lemma subPNn_n_Sm : forall (n m : nat), sub_PNn n (S m) = inci (sub_PNn n m).
  induction n; try reflexivity.
  intros m. rewrite ?subPNn_Sn_m.
  rewrite IHn. reflexivity.
  Defined.

Lemma subPNn_eq_Paddn : forall (n m : nat), sub_PNn n m = P (addn n m).
  induction n. try reflexivity.
  intros m. rewrite ?subPNn_Sn_m.
  rewrite IHn. rewrite addn_Sn_m.
  rewrite inci_Pn.
  reflexivity.
  Defined.

Fixpoint sub_NPn (n1 n2 : nat) :=
  match n1 with
  | O => N n2
  | S n1' => deci (sub_NPn n1' n2)
  end.

Lemma subNPn_n_O : forall (n : nat), sub_NPn n O = N n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  rewrite deci_Nn.
  reflexivity.
  Defined.

Lemma subNPn_O_m : forall (m : nat), sub_NPn O m = N m.
  reflexivity.
  Defined.

Lemma subNPn_Sn_m : forall (n m : nat), sub_NPn (S n) m = deci (sub_NPn n m).
  reflexivity.
  Defined.

Lemma subNPn_n_Sm : forall (n m : nat), sub_NPn n (S m) = deci (sub_NPn n m).
  induction n; try reflexivity.
  intros m. rewrite ?subNPn_Sn_m.
  rewrite IHn. reflexivity.
  Defined.

Lemma subNPn_eq_Naddn : forall (n m : nat), sub_NPn n m = N (addn n m).
  induction n; try reflexivity.
  intros m. rewrite ?subNPn_Sn_m.
  simpl.
  rewrite IHn.
  rewrite deci_Nn.
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

Lemma subNNn_n_O : forall (n : nat), sub_NNn n O = N n.
  induction n; try reflexivity.
  simpl; rewrite pz_equals_nz; reflexivity.
  Defined.

Lemma subNNn_O_m : forall (m : nat), sub_NNn O m = P m.
  reflexivity.
  Defined.

Lemma subNNn_Sn_Sm : forall (n m : nat), sub_NNn (S n) (S m) = sub_NNn n m.
  reflexivity.
  Defined.

Lemma subNNn_n_Sm : forall (n m : nat), sub_NNn n (S m) = inci (sub_NNn n m).
  induction n; try reflexivity.
  destruct m.
  rewrite subNNn_n_O. simpl.
  rewrite subNNn_n_O. reflexivity.
  rewrite ?subNNn_Sn_Sm.
  rewrite IHn. reflexivity.
  Defined.

Lemma subNNn_Sn_m : forall (n m : nat), sub_NNn (S n) m = deci (sub_NNn n m).
  induction n; try reflexivity.
  destruct m; try reflexivity.
  rewrite ?subNNn_Sn_Sm.
  rewrite IHn. reflexivity.
  Defined.

Lemma subNNn_n_n : forall (n : nat), sub_NNn n n = P O.
  induction n; try reflexivity.
  rewrite subNNn_Sn_Sm. assumption.
  Defined.

Lemma subNNn_anticomm : forall (n m : nat), sub_NNn n m = neg (sub_NNn m n).
  induction n; intros m.
  rewrite subNNn_O_m; rewrite subNNn_n_O.
  rewrite neg_Nn.
  reflexivity.
  rewrite subNNn_Sn_m. rewrite subNNn_n_Sm.
  rewrite neg_inci.
  rewrite IHn.
  reflexivity.
  Defined.

Lemma subPPn_neg_subNNn : forall (n m : nat), sub_PPn n m = neg (sub_NNn n m).
  induction n; destruct m; try reflexivity.
  simpl; rewrite pz_equals_nz; try reflexivity.
  rewrite subPPn_Sn_Sm.
  rewrite subNNn_Sn_Sm.
  rewrite IHn.
  reflexivity.
  Defined.

Lemma subPNn_neg_subNPn : forall (n m : nat), sub_PNn n m = neg (sub_NPn n m).
  induction n; destruct m; try reflexivity.
  simpl. rewrite subPNn_n_O. rewrite subNPn_n_O. simpl. reflexivity.
  rewrite ?subPNn_Sn_m; rewrite ?subNPn_Sn_m.
  rewrite ?subPNn_n_Sm; rewrite ?subNPn_n_Sm.
  rewrite IHn.
  rewrite ?neg_deci.
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

Lemma addi_PP : forall (n m : nat), addi (P n) (P m) = sub_PNn n m.
  reflexivity.
  Defined.

Lemma addi_PN : forall (n m : nat), addi (P n) (N m) = sub_PPn n m.
  reflexivity.
  Defined.

Lemma addi_NP : forall (n m : nat), addi (N n) (P m) = sub_NNn n m.
  reflexivity.
  Defined.

Lemma addi_NN : forall (n m : nat), addi (N n) (N m) = sub_NPn n m.
  reflexivity.
  Defined.

Lemma subi_PP : forall (n m : nat), subi (P n) (P m) = sub_PPn n m.
  reflexivity.
  Defined.

Lemma subi_PN : forall (n m : nat), subi (P n) (N m) = sub_PNn n m.
  reflexivity.
  Defined.

Lemma subi_NP : forall (n m : nat), subi (N n) (P m) = sub_NPn n m.
  reflexivity.
  Defined.

Lemma subi_NN : forall (n m : nat), subi (N n) (N m) = sub_NNn n m.
  reflexivity.
  Defined.

Lemma addi_i_PO : forall (i : int), addi i (P O) = i.
  destruct i.
  rewrite addi_PP. rewrite subPNn_n_O. reflexivity.
  rewrite addi_NP. rewrite subNNn_n_O. reflexivity.
  Defined.

Lemma addi_PO_j : forall (j : int), addi (P O) j = j.
  destruct j.
  rewrite addi_PP. rewrite subPNn_O_m. reflexivity.
  rewrite addi_PN. rewrite subPPn_O_m. reflexivity.
  Defined.

Lemma subi_i_PO : forall (i : int), subi i (P O) = i.
  destruct i.
  rewrite subi_PP. rewrite subPPn_n_O. reflexivity.
  rewrite subi_NP. rewrite subNPn_n_O. reflexivity.
  Defined.

Lemma subi_PO_j : forall (j : int), subi (P O) j = neg j.
  destruct j.
  rewrite subi_PP. rewrite subPPn_O_m. rewrite neg_Pn. reflexivity.
  rewrite subi_PN. rewrite subPNn_O_m. reflexivity.
  Defined.

Lemma addi_i_negi : forall (i : int), addi i (neg i) = P O.
  destruct i.
  rewrite neg_Pn. rewrite addi_PN. rewrite subPPn_n_n. reflexivity.
  rewrite neg_Nn. rewrite addi_NP. rewrite subNNn_n_n. reflexivity.
  Defined.

Lemma subi_i_i : forall (i : int), subi i i = P O.


