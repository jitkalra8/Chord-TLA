
------------------------- MODULE Chord ------------------------
EXTENDS Naturals, TLC, Sequences
  
CONSTANT N

Nodes == 1..N
max(x,y) == IF x < y THEN y ELSE x
(*permNodes == Permutations(Nodes)*)

(* --algorithm Test
      variables 
      matrix = [row \in Nodes |-> [column \in Nodes |-> 9 ]];
      reach = [row \in Nodes |-> [column \in Nodes |-> 0 ]];
      succ = [row \in Nodes |->  9 ];
      succ2 = [row \in Nodes |-> 9 ];
      newsucc = [row \in Nodes |-> 9];
      prdc = [row \in Nodes |-> 9];
      canfail = 0;
      canjoin = 0;
      isalor = TRUE;
      isamor = TRUE;
      (*hsbest = TRUE;*)
      
      
      define
        between( x, y, z) ==
            \/ x < z /\ x < y /\ y < z
            \/ x > z /\ \/ x < z
                        \/ y < z
      end define;
      
       macro fillvalue(row, column, val)
       begin
        matrix[row][column] := val;
       end macro;
      
       procedure alor()  (* At Least One Ring *)
       variables flag = 0, j = 1..N, p2;
       begin
          alr1: while j # {} do 
                    p2 := CHOOSE l \in j:TRUE;
                    if reach[p2][p2] = 1 then
                        flag := 1;
                    end if;
                    j := j \ {p2};
                end while;   
                if flag = 0 then
                    isalor := FALSE;
                    assert isalor;
                end if;
       return;
       end procedure;
             
       procedure amor() (* At Most One Ring *)
       variables j=1..N, i=1..N , p, q;
       begin
       amr0: if j # {} then
                   i := Len(j)+1..N;
             amr2: while j # {} do
                   p := CHOOSE k \in j:TRUE; q := CHOOSE r \in i: TRUE;
                        if reach[p][p] = 1 /\ reach[q][q] = 1 then
                            if reach[p][q] = 0 \/ reach[q][p] = 0 then
                                isamor := FALSE;
                                assert isamor;
                            end if;
                        end if;
                 amr3:  i := i \ {q};
                        if i = {} /\ j # {} then
                            j := j \ {p};
                 amr4:      i := Len(j)+1..N;
                        end if;
                end while;
              end if;   
       ret: return;
       end procedure;      

       process Site \in Nodes
       variables temp;          
       begin
       lbl5: fillvalue(self,1,4);
       lbl7: call alor();
       lbl8: call amor();
       
       end process;
  end algorithm
*)


\* BEGIN TRANSLATION 
\* Procedure variable j of procedure alor at line 39 col 28 changed to j_
CONSTANT defaultInitValue
VARIABLES matrix, reach, succ, succ2, newsucc, prdc, canfail, canjoin, isalor, 
          isamor, pc, stack

(* define statement *)
between( x, y, z) ==
    \/ x < z /\ x < y /\ y < z
    \/ x > z /\ \/ x < z
                \/ y < z

VARIABLES flag, j_, p2, j, i, p, q, temp

vars == << matrix, reach, succ, succ2, newsucc, prdc, canfail, canjoin, 
           isalor, isamor, pc, stack, flag, j_, p2, j, i, p, q, temp >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ matrix = [row \in Nodes |-> [column \in Nodes |-> 9 ]]
        /\ reach = [row \in Nodes |-> [column \in Nodes |-> 0 ]]
        /\ succ = [row \in Nodes |->  9 ]
        /\ succ2 = [row \in Nodes |-> 9 ]
        /\ newsucc = [row \in Nodes |-> 9]
        /\ prdc = [row \in Nodes |-> 9]
        /\ canfail = 0
        /\ canjoin = 0
        /\ isalor = TRUE
        /\ isamor = TRUE
        (* Procedure alor *)
        /\ flag = [ self \in ProcSet |-> 0]
        /\ j_ = [ self \in ProcSet |-> 1..N]
        /\ p2 = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure amor *)
        /\ j = [ self \in ProcSet |-> 1..N]
        /\ i = [ self \in ProcSet |-> 1..N]
        /\ p = [ self \in ProcSet |-> defaultInitValue]
        /\ q = [ self \in ProcSet |-> defaultInitValue]
        (* Process Site *)
        /\ temp = [self \in Nodes |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "lbl5"]

alr1(self) == /\ pc[self] = "alr1"
              /\ IF j_[self] # {}
                    THEN /\ p2' = [p2 EXCEPT ![self] = CHOOSE l \in j_[self]:TRUE]
                         /\ IF reach[p2'[self]][p2'[self]] = 1
                               THEN /\ flag' = [flag EXCEPT ![self] = 1]
                               ELSE /\ TRUE
                                    /\ flag' = flag
                         /\ j_' = [j_ EXCEPT ![self] = j_[self] \ {p2'[self]}]
                         /\ pc' = [pc EXCEPT ![self] = "alr1"]
                         /\ UNCHANGED << isalor, stack >>
                    ELSE /\ IF flag[self] = 0
                               THEN /\ isalor' = FALSE
                                    /\ Assert(isalor', 
                                              "Failure of assertion at line 50, column 21.")
                               ELSE /\ TRUE
                                    /\ UNCHANGED isalor
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ flag' = [flag EXCEPT ![self] = Head(stack[self]).flag]
                         /\ j_' = [j_ EXCEPT ![self] = Head(stack[self]).j_]
                         /\ p2' = [p2 EXCEPT ![self] = Head(stack[self]).p2]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << matrix, reach, succ, succ2, newsucc, prdc, 
                              canfail, canjoin, isamor, j, i, p, q, temp >>

alor(self) == alr1(self)

amr0(self) == /\ pc[self] = "amr0"
              /\ IF j[self] # {}
                    THEN /\ i' = [i EXCEPT ![self] = Len(j[self])+1..N]
                         /\ pc' = [pc EXCEPT ![self] = "amr2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ret"]
                         /\ i' = i
              /\ UNCHANGED << matrix, reach, succ, succ2, newsucc, prdc, 
                              canfail, canjoin, isalor, isamor, stack, flag, 
                              j_, p2, j, p, q, temp >>

amr2(self) == /\ pc[self] = "amr2"
              /\ IF j[self] # {}
                    THEN /\ p' = [p EXCEPT ![self] = CHOOSE k \in j[self]:TRUE]
                         /\ q' = [q EXCEPT ![self] = CHOOSE r \in i[self]: TRUE]
                         /\ IF reach[p'[self]][p'[self]] = 1 /\ reach[q'[self]][q'[self]] = 1
                               THEN /\ IF reach[p'[self]][q'[self]] = 0 \/ reach[q'[self]][p'[self]] = 0
                                          THEN /\ isamor' = FALSE
                                               /\ Assert(isamor', 
                                                         "Failure of assertion at line 65, column 33.")
                                          ELSE /\ TRUE
                                               /\ UNCHANGED isamor
                               ELSE /\ TRUE
                                    /\ UNCHANGED isamor
                         /\ pc' = [pc EXCEPT ![self] = "amr3"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ret"]
                         /\ UNCHANGED << isamor, p, q >>
              /\ UNCHANGED << matrix, reach, succ, succ2, newsucc, prdc, 
                              canfail, canjoin, isalor, stack, flag, j_, p2, j, 
                              i, temp >>

amr3(self) == /\ pc[self] = "amr3"
              /\ i' = [i EXCEPT ![self] = i[self] \ {q[self]}]
              /\ IF i'[self] = {} /\ j[self] # {}
                    THEN /\ j' = [j EXCEPT ![self] = j[self] \ {p[self]}]
                         /\ pc' = [pc EXCEPT ![self] = "amr4"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "amr2"]
                         /\ j' = j
              /\ UNCHANGED << matrix, reach, succ, succ2, newsucc, prdc, 
                              canfail, canjoin, isalor, isamor, stack, flag, 
                              j_, p2, p, q, temp >>

amr4(self) == /\ pc[self] = "amr4"
              /\ i' = [i EXCEPT ![self] = Len(j[self])+1..N]
              /\ pc' = [pc EXCEPT ![self] = "amr2"]
              /\ UNCHANGED << matrix, reach, succ, succ2, newsucc, prdc, 
                              canfail, canjoin, isalor, isamor, stack, flag, 
                              j_, p2, j, p, q, temp >>

ret(self) == /\ pc[self] = "ret"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
             /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
             /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
             /\ q' = [q EXCEPT ![self] = Head(stack[self]).q]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << matrix, reach, succ, succ2, newsucc, prdc, 
                             canfail, canjoin, isalor, isamor, flag, j_, p2, 
                             temp >>

amor(self) == amr0(self) \/ amr2(self) \/ amr3(self) \/ amr4(self)
                 \/ ret(self)

lbl5(self) == /\ pc[self] = "lbl5"
              /\ matrix' = [matrix EXCEPT ![self][1] = 4]
              /\ pc' = [pc EXCEPT ![self] = "lbl7"]
              /\ UNCHANGED << reach, succ, succ2, newsucc, prdc, canfail, 
                              canjoin, isalor, isamor, stack, flag, j_, p2, j, 
                              i, p, q, temp >>

lbl7(self) == /\ pc[self] = "lbl7"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "alor",
                                                       pc        |->  "lbl8",
                                                       flag      |->  flag[self],
                                                       j_        |->  j_[self],
                                                       p2        |->  p2[self] ] >>
                                                   \o stack[self]]
              /\ flag' = [flag EXCEPT ![self] = 0]
              /\ j_' = [j_ EXCEPT ![self] = 1..N]
              /\ p2' = [p2 EXCEPT ![self] = defaultInitValue]
              /\ pc' = [pc EXCEPT ![self] = "alr1"]
              /\ UNCHANGED << matrix, reach, succ, succ2, newsucc, prdc, 
                              canfail, canjoin, isalor, isamor, j, i, p, q, 
                              temp >>

lbl8(self) == /\ pc[self] = "lbl8"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "amor",
                                                       pc        |->  "Done",
                                                       j         |->  j[self],
                                                       i         |->  i[self],
                                                       p         |->  p[self],
                                                       q         |->  q[self] ] >>
                                                   \o stack[self]]
              /\ j' = [j EXCEPT ![self] = 1..N]
              /\ i' = [i EXCEPT ![self] = 1..N]
              /\ p' = [p EXCEPT ![self] = defaultInitValue]
              /\ q' = [q EXCEPT ![self] = defaultInitValue]
              /\ pc' = [pc EXCEPT ![self] = "amr0"]
              /\ UNCHANGED << matrix, reach, succ, succ2, newsucc, prdc, 
                              canfail, canjoin, isalor, isamor, flag, j_, p2, 
                              temp >>

Site(self) == lbl5(self) \/ lbl7(self) \/ lbl8(self)

Next == (\E self \in ProcSet: alor(self) \/ amor(self))
           \/ (\E self \in Nodes: Site(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
==================================================================================


============================================================================
