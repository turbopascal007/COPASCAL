program koren (input, output);
                       {            x   +  y  /  x          }
{ _    }               {             i            i         }
{ûy=0  }               { x    =  --------------------       }
{       _}             {  i+1                               }
{x1=x0+ûy}             {                  2                 }


Const
  C = 5;

Var
  N   : Integer;
  X,Y : Real;

Function Kor (X, Y : Real) : Real;
Begin
  Kor := X+Sqr(Y)
End;

Function Kor2 (Y : Real) : Real;
Var
  X : Real;
  I : Integer;
Begin
  X := 1;
  For I := 1 to C do
    X := (X+Y/X)/2;
  Kor2 := X
End;

Begin
  Y := 2;
{  X := 1;
  For N := 1 to C do
    Begin
      WriteLn (X:5, X*X:10);
      X := Kor (X, Y)
    End;}
  WriteLn (Kor2(Y))
End.
