#Link: https://t-t-h-n-e-w.blogspot.com/2020/10/mot-chuong-trinh-nho-de-kiem-tra-bat-dang-thuc.html
#Checking inequality
tfx:=proc(ineq)
local var;
if nops({args})>=2 then var:=args[2];
else var:=indets(ineq);fi;
print(`First checking begin..`);
tff(ineq,[op(var)]);
print(`finished in first checking.`);
print(`============================================================================`);
print(`Second checking begin..`);
tf(ineq,[op(var)]);
print(`finished in second checking.`);
print(`============================================================================`);
end:
tff:=proc(ineq)
local g,var,tm,vvar,f,lst,temp,i,N;
print(ineq);
g:=rhs(ineq)-lhs(ineq);
tm:=time();
if nops({args})>=2 then var:=args[2];
else var:=indets(g);fi;
#var:={};
print(`Starting testing..`);
print([op(var)]);
lst:=1/rand(1..1000);
N:=10000;
to N do
temp:={};for i from 1 to nops(var) do temp:=temp union  {var[i]=lst()};od;
if evalf(subs(temp,g),200)<0 then print(`outside-data:`,[op(temp)]),print(`The inequality doesn't hold !`),print(`time is:`,time()-tm);
RETURN(); return fi;od;
end:
tf:=proc(ineq)
local g,var,tm,vvar,f,lst,temp,i,N;
print(ineq);
g:=rhs(ineq)-lhs(ineq);
tm:=time();
if nops({args})>=2 then var:=args[2];
else var:=indets(g);fi;
print(`Starting testing..`);
g:=rhs(ineq)-lhs(ineq);
tm:=time();
print([op(var)]);
lst:=rand(1..1000);
N:=10000;
to N do
temp:={};for i from 1 to nops(var) do temp:=temp union  {var[i]=lst()};od;
if evalf(subs(temp,g),200)<0 then print(`outside-data:`,[op(temp)]),print(`The inequality doesn't hold !`),print(`time is:`,time()-tm); return();fi;od;
end:
