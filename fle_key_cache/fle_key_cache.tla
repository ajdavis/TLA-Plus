--------------------------- MODULE fle_key_cache ---------------------------

EXTENDS Sequences, Integers, TLC, FiniteSets

(* --fair algorithm fle_key_cache

variables lock = [r |-> FALSE, g |-> FALSE, b |-> 0],
          key_cache = [key0 |-> "null"],
          \* For each key, process "0" means no process fetched this key.
          which_process_fetched_key = [key0 |-> 0]
          
define
    all_fetched == \A key \in DOMAIN key_cache: key \notin {"null", "pending"}
    each_key_fetched_by_one_process ==
        \A key \in DOMAIN which_process_fetched_key: which_process_fetched_key[key] /= 0
end define;

(***************************************************************************

Readers-writer lock from https://en.wikipedia.org/wiki/Readers%E2%80%93writer_lock#Using_two_mutexes
Credit to Michael Raynal.
r ("reader") and g ("global") are locks, if TRUE then locked. b is the number of readers.
In libmongocrypt, use a pthread_rwlock_t or the Windows equivalent instead. 
Although there is a concept of an upgradable RW lock it's prone to deadlock:
     https://oroboro.com/upgradable-read-write-locks/
So use a regular RW lock, which is what systems provide for us anyway.

***************************************************************************)

procedure begin_read() begin 
    BEGIN_READ: 
        await ~lock.r;
        lock.r := TRUE;
    BEGIN_READ_INCREMENT_B:
        lock.b := lock.b + 1;
    BEGIN_READ_CHECK_B:
        if lock.b = 1 then
            BEGIN_READ_AWAIT_G:
                await ~lock.g;
                lock.g := TRUE;
        end if;
    BEGIN_READ_UNLOCK_R:
        lock.r := FALSE;
    BEGIN_READ_DONE:
    return;
end procedure

procedure end_read() begin 
    END_READ: 
        await ~lock.r;
        lock.r := TRUE;
    END_READ_DECREMENT_B:
        lock.b := lock.b - 1;
        if lock.b = 0 then
            END_READ_UNLOCK_G:
                assert lock.g;
                lock.g := FALSE;
        end if;
    END_READ_UNLOCK_R:
        lock.r := FALSE;
    END_READ_DONE:
    return;
end procedure

procedure begin_write() begin 
    BEGIN_WRITE: 
        await ~lock.g;
        lock.g := TRUE;
    BEGIN_WRITE_DONE:
    return;
end procedure

procedure end_write() begin 
    END_WRITE:
        assert lock.g;
        lock.g := FALSE;
    return;
end procedure

(***************************************************************************
Fetch a key from Amazon's KMS service and put it in a shared cache.

- Lock the cache in "read" mode.
- If the key is "pending" because another thread is fetching it, wait.
- Else if the key is not "null" then it has been fetched; return.
- Else drop the read lock, get the write lock, check the key is still "null",
  mark the key "pending" to block other threads, and start fetching.
- On success, cache the key and return.
- On failure, retry.

***************************************************************************)

process get_key \in 1..2
    variables got_key = FALSE;
begin
    GET_KEY:
        call begin_read();
    GET_KEY_READ_CACHE0:
        if key_cache.key0 = "pending" then
            \* Another thread is fetching this key, await its success/failure.
            call end_read();
    GET_KEY_READ_CACHE1:        
            await key_cache.key0 /= "pending";
            \* Try again.
            goto GET_KEY;                    
        elsif key_cache.key0 /= "null" then
            \* Key is cached. In real life, return the key to the caller.
            goto Done;
        end if;
    GET_KEY_WRITE_PENDING0:
        call end_read();
    GET_KEY_WRITE_PENDING1:
        call begin_write();
    GET_KEY_WRITE_PENDING2:
        \* We dropped the lock in end_read() above, so check again.
        if key_cache.key0 /= "null" then
            call end_write();
            goto GET_KEY;
        end if;
    GET_KEY_WRITE_PENDING3:
        key_cache.key0 := "pending";
        \* which_process_fetched_key is not part of the real algorithm, it's for
        \* checking the algorithm's correctness.
        assert which_process_fetched_key.key0 = 0;
        which_process_fetched_key.key0 := self;
    GET_KEY_WRITE_KEY0:
        \* Unlock while we fetch the key.
        call end_write();
    GET_KEY_WRITE_KEY1:
        call begin_write();
    GET_KEY_START_FETCHING:        
        \* Still "pending", no other process can change it.
        assert key_cache.key0 = "pending";
        either 
    GET_KEY_SUCCEEDED:
            key_cache.key0 := "key_material";        
            got_key := TRUE;
        or
    GET_KEY_FAILED:
            \* Failed to fetch the key.
            key_cache.key0 := "null";
            got_key := FALSE;
            assert which_process_fetched_key.key0 = self;
            which_process_fetched_key.key0 := 0;
        end either;
    GET_KEY_WRITE_KEY3:
        call end_write();
    GET_KEY_MAYBE_RETRY:
        if ~got_key then
            goto GET_KEY;
        end if;
end process

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES lock, key_cache, which_process_fetched_key, pc, stack

(* define statement *)
all_fetched == \A key \in DOMAIN key_cache: key \notin {"null", "pending"}
each_key_fetched_by_one_process ==
    \A key \in DOMAIN which_process_fetched_key: which_process_fetched_key[key] /= 0

VARIABLE got_key

vars == << lock, key_cache, which_process_fetched_key, pc, stack, got_key >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ lock = [r |-> FALSE, g |-> FALSE, b |-> 0]
        /\ key_cache = [key0 |-> "null"]
        /\ which_process_fetched_key = [key0 |-> 0]
        (* Process get_key *)
        /\ got_key = [self \in 1..2 |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "GET_KEY"]

BEGIN_READ(self) == /\ pc[self] = "BEGIN_READ"
                    /\ ~lock.r
                    /\ lock' = [lock EXCEPT !.r = TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "BEGIN_READ_INCREMENT_B"]
                    /\ UNCHANGED << key_cache, which_process_fetched_key, 
                                    stack, got_key >>

BEGIN_READ_INCREMENT_B(self) == /\ pc[self] = "BEGIN_READ_INCREMENT_B"
                                /\ lock' = [lock EXCEPT !.b = lock.b + 1]
                                /\ pc' = [pc EXCEPT ![self] = "BEGIN_READ_CHECK_B"]
                                /\ UNCHANGED << key_cache, 
                                                which_process_fetched_key, 
                                                stack, got_key >>

BEGIN_READ_CHECK_B(self) == /\ pc[self] = "BEGIN_READ_CHECK_B"
                            /\ IF lock.b = 1
                                  THEN /\ pc' = [pc EXCEPT ![self] = "BEGIN_READ_AWAIT_G"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "BEGIN_READ_UNLOCK_R"]
                            /\ UNCHANGED << lock, key_cache, 
                                            which_process_fetched_key, stack, 
                                            got_key >>

BEGIN_READ_AWAIT_G(self) == /\ pc[self] = "BEGIN_READ_AWAIT_G"
                            /\ ~lock.g
                            /\ lock' = [lock EXCEPT !.g = TRUE]
                            /\ pc' = [pc EXCEPT ![self] = "BEGIN_READ_UNLOCK_R"]
                            /\ UNCHANGED << key_cache, 
                                            which_process_fetched_key, stack, 
                                            got_key >>

BEGIN_READ_UNLOCK_R(self) == /\ pc[self] = "BEGIN_READ_UNLOCK_R"
                             /\ lock' = [lock EXCEPT !.r = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = "BEGIN_READ_DONE"]
                             /\ UNCHANGED << key_cache, 
                                             which_process_fetched_key, stack, 
                                             got_key >>

BEGIN_READ_DONE(self) == /\ pc[self] = "BEGIN_READ_DONE"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << lock, key_cache, 
                                         which_process_fetched_key, got_key >>

begin_read(self) == BEGIN_READ(self) \/ BEGIN_READ_INCREMENT_B(self)
                       \/ BEGIN_READ_CHECK_B(self)
                       \/ BEGIN_READ_AWAIT_G(self)
                       \/ BEGIN_READ_UNLOCK_R(self)
                       \/ BEGIN_READ_DONE(self)

END_READ(self) == /\ pc[self] = "END_READ"
                  /\ ~lock.r
                  /\ lock' = [lock EXCEPT !.r = TRUE]
                  /\ pc' = [pc EXCEPT ![self] = "END_READ_DECREMENT_B"]
                  /\ UNCHANGED << key_cache, which_process_fetched_key, stack, 
                                  got_key >>

END_READ_DECREMENT_B(self) == /\ pc[self] = "END_READ_DECREMENT_B"
                              /\ lock' = [lock EXCEPT !.b = lock.b - 1]
                              /\ IF lock'.b = 0
                                    THEN /\ pc' = [pc EXCEPT ![self] = "END_READ_UNLOCK_G"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "END_READ_UNLOCK_R"]
                              /\ UNCHANGED << key_cache, 
                                              which_process_fetched_key, stack, 
                                              got_key >>

END_READ_UNLOCK_G(self) == /\ pc[self] = "END_READ_UNLOCK_G"
                           /\ Assert(lock.g, 
                                     "Failure of assertion at line 56, column 17.")
                           /\ lock' = [lock EXCEPT !.g = FALSE]
                           /\ pc' = [pc EXCEPT ![self] = "END_READ_UNLOCK_R"]
                           /\ UNCHANGED << key_cache, 
                                           which_process_fetched_key, stack, 
                                           got_key >>

END_READ_UNLOCK_R(self) == /\ pc[self] = "END_READ_UNLOCK_R"
                           /\ lock' = [lock EXCEPT !.r = FALSE]
                           /\ pc' = [pc EXCEPT ![self] = "END_READ_DONE"]
                           /\ UNCHANGED << key_cache, 
                                           which_process_fetched_key, stack, 
                                           got_key >>

END_READ_DONE(self) == /\ pc[self] = "END_READ_DONE"
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << lock, key_cache, 
                                       which_process_fetched_key, got_key >>

end_read(self) == END_READ(self) \/ END_READ_DECREMENT_B(self)
                     \/ END_READ_UNLOCK_G(self) \/ END_READ_UNLOCK_R(self)
                     \/ END_READ_DONE(self)

BEGIN_WRITE(self) == /\ pc[self] = "BEGIN_WRITE"
                     /\ ~lock.g
                     /\ lock' = [lock EXCEPT !.g = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = "BEGIN_WRITE_DONE"]
                     /\ UNCHANGED << key_cache, which_process_fetched_key, 
                                     stack, got_key >>

BEGIN_WRITE_DONE(self) == /\ pc[self] = "BEGIN_WRITE_DONE"
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << lock, key_cache, 
                                          which_process_fetched_key, got_key >>

begin_write(self) == BEGIN_WRITE(self) \/ BEGIN_WRITE_DONE(self)

END_WRITE(self) == /\ pc[self] = "END_WRITE"
                   /\ Assert(lock.g, 
                             "Failure of assertion at line 75, column 9.")
                   /\ lock' = [lock EXCEPT !.g = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << key_cache, which_process_fetched_key, 
                                   got_key >>

end_write(self) == END_WRITE(self)

GET_KEY(self) == /\ pc[self] = "GET_KEY"
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "begin_read",
                                                          pc        |->  "GET_KEY_READ_CACHE0" ] >>
                                                      \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "BEGIN_READ"]
                 /\ UNCHANGED << lock, key_cache, which_process_fetched_key, 
                                 got_key >>

GET_KEY_READ_CACHE0(self) == /\ pc[self] = "GET_KEY_READ_CACHE0"
                             /\ IF key_cache.key0 = "pending"
                                   THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "end_read",
                                                                                 pc        |->  "GET_KEY_READ_CACHE1" ] >>
                                                                             \o stack[self]]
                                        /\ pc' = [pc EXCEPT ![self] = "END_READ"]
                                   ELSE /\ IF key_cache.key0 /= "null"
                                              THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "GET_KEY_WRITE_PENDING0"]
                                        /\ stack' = stack
                             /\ UNCHANGED << lock, key_cache, 
                                             which_process_fetched_key, 
                                             got_key >>

GET_KEY_READ_CACHE1(self) == /\ pc[self] = "GET_KEY_READ_CACHE1"
                             /\ key_cache.key0 /= "pending"
                             /\ pc' = [pc EXCEPT ![self] = "GET_KEY"]
                             /\ UNCHANGED << lock, key_cache, 
                                             which_process_fetched_key, stack, 
                                             got_key >>

GET_KEY_WRITE_PENDING0(self) == /\ pc[self] = "GET_KEY_WRITE_PENDING0"
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "end_read",
                                                                         pc        |->  "GET_KEY_WRITE_PENDING1" ] >>
                                                                     \o stack[self]]
                                /\ pc' = [pc EXCEPT ![self] = "END_READ"]
                                /\ UNCHANGED << lock, key_cache, 
                                                which_process_fetched_key, 
                                                got_key >>

GET_KEY_WRITE_PENDING1(self) == /\ pc[self] = "GET_KEY_WRITE_PENDING1"
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "begin_write",
                                                                         pc        |->  "GET_KEY_WRITE_PENDING2" ] >>
                                                                     \o stack[self]]
                                /\ pc' = [pc EXCEPT ![self] = "BEGIN_WRITE"]
                                /\ UNCHANGED << lock, key_cache, 
                                                which_process_fetched_key, 
                                                got_key >>

GET_KEY_WRITE_PENDING2(self) == /\ pc[self] = "GET_KEY_WRITE_PENDING2"
                                /\ IF key_cache.key0 /= "null"
                                      THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "end_write",
                                                                                    pc        |->  "GET_KEY" ] >>
                                                                                \o stack[self]]
                                           /\ pc' = [pc EXCEPT ![self] = "END_WRITE"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "GET_KEY_WRITE_PENDING3"]
                                           /\ stack' = stack
                                /\ UNCHANGED << lock, key_cache, 
                                                which_process_fetched_key, 
                                                got_key >>

GET_KEY_WRITE_PENDING3(self) == /\ pc[self] = "GET_KEY_WRITE_PENDING3"
                                /\ key_cache' = [key_cache EXCEPT !.key0 = "pending"]
                                /\ Assert(which_process_fetched_key.key0 = 0, 
                                          "Failure of assertion at line 124, column 9.")
                                /\ which_process_fetched_key' = [which_process_fetched_key EXCEPT !.key0 = self]
                                /\ pc' = [pc EXCEPT ![self] = "GET_KEY_WRITE_KEY0"]
                                /\ UNCHANGED << lock, stack, got_key >>

GET_KEY_WRITE_KEY0(self) == /\ pc[self] = "GET_KEY_WRITE_KEY0"
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "end_write",
                                                                     pc        |->  "GET_KEY_WRITE_KEY1" ] >>
                                                                 \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "END_WRITE"]
                            /\ UNCHANGED << lock, key_cache, 
                                            which_process_fetched_key, got_key >>

GET_KEY_WRITE_KEY1(self) == /\ pc[self] = "GET_KEY_WRITE_KEY1"
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "begin_write",
                                                                     pc        |->  "GET_KEY_START_FETCHING" ] >>
                                                                 \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "BEGIN_WRITE"]
                            /\ UNCHANGED << lock, key_cache, 
                                            which_process_fetched_key, got_key >>

GET_KEY_START_FETCHING(self) == /\ pc[self] = "GET_KEY_START_FETCHING"
                                /\ Assert(key_cache.key0 = "pending", 
                                          "Failure of assertion at line 133, column 9.")
                                /\ \/ /\ pc' = [pc EXCEPT ![self] = "GET_KEY_SUCCEEDED"]
                                   \/ /\ pc' = [pc EXCEPT ![self] = "GET_KEY_FAILED"]
                                /\ UNCHANGED << lock, key_cache, 
                                                which_process_fetched_key, 
                                                stack, got_key >>

GET_KEY_SUCCEEDED(self) == /\ pc[self] = "GET_KEY_SUCCEEDED"
                           /\ key_cache' = [key_cache EXCEPT !.key0 = "key_material"]
                           /\ got_key' = [got_key EXCEPT ![self] = TRUE]
                           /\ pc' = [pc EXCEPT ![self] = "GET_KEY_WRITE_KEY3"]
                           /\ UNCHANGED << lock, which_process_fetched_key, 
                                           stack >>

GET_KEY_FAILED(self) == /\ pc[self] = "GET_KEY_FAILED"
                        /\ key_cache' = [key_cache EXCEPT !.key0 = "null"]
                        /\ got_key' = [got_key EXCEPT ![self] = FALSE]
                        /\ Assert(which_process_fetched_key.key0 = self, 
                                  "Failure of assertion at line 143, column 13.")
                        /\ which_process_fetched_key' = [which_process_fetched_key EXCEPT !.key0 = 0]
                        /\ pc' = [pc EXCEPT ![self] = "GET_KEY_WRITE_KEY3"]
                        /\ UNCHANGED << lock, stack >>

GET_KEY_WRITE_KEY3(self) == /\ pc[self] = "GET_KEY_WRITE_KEY3"
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "end_write",
                                                                     pc        |->  "GET_KEY_MAYBE_RETRY" ] >>
                                                                 \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "END_WRITE"]
                            /\ UNCHANGED << lock, key_cache, 
                                            which_process_fetched_key, got_key >>

GET_KEY_MAYBE_RETRY(self) == /\ pc[self] = "GET_KEY_MAYBE_RETRY"
                             /\ IF ~got_key[self]
                                   THEN /\ pc' = [pc EXCEPT ![self] = "GET_KEY"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << lock, key_cache, 
                                             which_process_fetched_key, stack, 
                                             got_key >>

get_key(self) == GET_KEY(self) \/ GET_KEY_READ_CACHE0(self)
                    \/ GET_KEY_READ_CACHE1(self)
                    \/ GET_KEY_WRITE_PENDING0(self)
                    \/ GET_KEY_WRITE_PENDING1(self)
                    \/ GET_KEY_WRITE_PENDING2(self)
                    \/ GET_KEY_WRITE_PENDING3(self)
                    \/ GET_KEY_WRITE_KEY0(self) \/ GET_KEY_WRITE_KEY1(self)
                    \/ GET_KEY_START_FETCHING(self)
                    \/ GET_KEY_SUCCEEDED(self) \/ GET_KEY_FAILED(self)
                    \/ GET_KEY_WRITE_KEY3(self)
                    \/ GET_KEY_MAYBE_RETRY(self)

Next == (\E self \in ProcSet:  \/ begin_read(self) \/ end_read(self)
                               \/ begin_write(self) \/ end_write(self))
           \/ (\E self \in 1..2: get_key(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


(***************************************************************************
See https://groups.google.com/forum/#!topic/tlaplus/7KLn9O-rwPo
and https://groups.google.com/forum/#!topic/tlaplus/FqGPF_2-ljE for discussions 
of adding strong fairness guarantees to PlusCal "EITHER" expressions
***************************************************************************)

FairSpec == Spec 
            /\ SF_vars(\E self \in ProcSet: GET_KEY_START_FETCHING(self) /\ pc'[self] = "GET_KEY_SUCCEEDED")

=============================================================================
\* Modification History
\* Last modified Sat Mar 09 21:08:08 EST 2019 by emptysquare
\* Created Mon Feb 18 19:13:25 EST 2019 by emptysquare
