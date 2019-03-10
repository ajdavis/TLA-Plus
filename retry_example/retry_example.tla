--------------------------- MODULE retry_example ---------------------------
EXTENDS Naturals, TLC

NumProcesses == 2

(*--algorithm retry_example

variables
    \* Both processes have not yet succeeded.
    succeeded = [p \in 1..NumProcesses |-> FALSE];

define
    all_succeeded == \A p \in 1..NumProcesses: succeeded[p]
end define;

fair process retry_example \in 1..NumProcesses
begin
    RETRY_BEGIN:
        either
            RETRY_SUCCEED:
                succeeded[self] := TRUE;
        or
            RETRY_ERROR:
                goto RETRY_BEGIN;
        end either;
end process;

end algorithm *)
\* BEGIN TRANSLATION
VARIABLES succeeded, pc

(* define statement *)
all_succeeded == \A p \in 1..NumProcesses: succeeded[p]


vars == << succeeded, pc >>

ProcSet == (1..NumProcesses)

Init == (* Global variables *)
        /\ succeeded = [p \in 1..NumProcesses |-> FALSE]
        /\ pc = [self \in ProcSet |-> "RETRY_BEGIN"]

RETRY_BEGIN(self) == /\ pc[self] = "RETRY_BEGIN"
                     /\ \/ /\ pc' = [pc EXCEPT ![self] = "RETRY_SUCCEED"]
                        \/ /\ pc' = [pc EXCEPT ![self] = "RETRY_ERROR"]
                     /\ UNCHANGED succeeded

RETRY_SUCCEED(self) == /\ pc[self] = "RETRY_SUCCEED"
                       /\ succeeded' = [succeeded EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "Done"]

RETRY_ERROR(self) == /\ pc[self] = "RETRY_ERROR"
                     /\ pc' = [pc EXCEPT ![self] = "RETRY_BEGIN"]
                     /\ UNCHANGED succeeded

retry_example(self) == RETRY_BEGIN(self) \/ RETRY_SUCCEED(self)
                          \/ RETRY_ERROR(self)

Next == (\E self \in 1..NumProcesses: retry_example(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NumProcesses : WF_vars(retry_example(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Nice way?
FairSpec == Spec /\ SF_vars(\E self \in ProcSet: RETRY_BEGIN(self) /\ pc'[self] = "RETRY_SUCCEED")

\* Hacky way
\*FairSpec == Spec /\ SF_vars(RETRY_BEGIN(1) /\ pc'[1] = "RETRY_SUCCEED") /\ SF_vars(RETRY_BEGIN(2) /\ pc'[2] = "RETRY_SUCCEED")

=============================================================================
\* Modification History
\* Last modified Sat Mar 09 11:24:40 EST 2019 by emptysquare
\* Created Sat Feb 23 10:29:54 EST 2019 by emptysquare
