Chord-TLA
=========

Given implementation file can be executed in TLA Toolbox by following below steps-

1. Create new spec having same name as module(file name).
2. Parse (File -> Parse Module) and Translate(File -> Translate PlusCal Algorithm)
3. Create new model (TLC Model Checker -> New Model) 
4. Provide constant value of N in general window of model. i.e 2 for now.  


This implementation will prove 2 properties of Chord 
1. Atmost one Ring. - At any point of time chord ring must have no more than one Ring.
2. Atleast one Ring. - At any point of time chord ring must not have more than one Ring.


The properties are being verified by use of assertions in the corresponding procedures in the file. If at any time the assertion is violated then error occurs and show the trace of failed assertions.
The failure scenario can be found by checking the stack variables in TLA Toolbox.


Note: Basic implementation has been done in collaboration with Prasidh. However, We are working on different properties of chord. 
