protect(A, B, C, GA, GB, GC, HA, HB, HC, Ha, Hb, Hc, IA, IB, IC, JA, JB, JC, Ja, Jb, Jc, Ra, Rb, Rc, a, b, c, ca, cb, cc, ha, hb, hc, ka, kb, kc, ma, mb, mc, ra, rb, rc, u, v, w, wa, wb, wc, x, x1, x2, x3, y, z);
print([Abel,AsSymmetric,BinetCauchy,Info,Lagrange,Lebesgue,Liouville]);
Info:=proc()
print("Calculate algebra with some identities - Version 1.0");
print("nknew6@gmail.com");
print(`Copyright(C) 2011-2020 by tthnew`);
end:
facElements:=proc(expr)
local oop,temp,i;
oop:={op(expr)};
temp:=0;for i to nops(oop) do temp:=temp+factor(oop[i]);od;
end:
sgm:=proc(expr)
   local rap,ex2,ex3,ex:
      rap:={x1=x2,x2=x3,x3=x1,a=b,b=c,c=a,A=B,B=C,C=A,x=y,y=z,z=x,u=v,v=w,w=u,ha=hb,hb=hc,hc=ha,Ra=Rb,Rb=Rc,Rc=Ra,ra=rb,rb=rc,rc=ra,ma=mb,mb=mc,mc=ma,wa=wb,wb=wc,wc=wa,ka=kb,kb=kc,kc=ka,
         HA=HB,HB=HC,HC=HA,IA=IB,IB=IC,
         IC=IA,Ha=Hb,Hb=Hc,Hc=Ha,A=B,B=C,C=A,Ra=Rb,Rb=Rc,Rc=Ra,GA=GB,GB=GC,
         GC=GA,JA=JB,JB=JC,JC=JA,ca=cb,cb=cc,cc=ca,Ja=Jb,Jb=Jc,Jc=Ja}:     
   ex2:=subs(rap,expr):
   ex3:=subs(rap,ex2):
   ex:=expr+ex2+ex3:
   RETURN(ex)
end:

pro:=proc(expr)
   local rap,ex2,ex3,ex:
      rap:={x1=x2,x2=x3,x3=x1,a=b,b=c,c=a,A=B,B=C,C=A,x=y,y=z,z=x,u=v,v=w,w=u,ha=hb,hb=hc,hc=ha,Ra=Rb,Rb=Rc,Rc=Ra,ra=rb,rb=rc,rc=ra,ma=mb,mb=mc,mc=ma,wa=wb,wb=wc,wc=wa,ka=kb,kb=kc,kc=ka,
         HA=HB,HB=HC,HC=HA,IA=IB,IB=IC,
         IC=IA,Ha=Hb,Hb=Hc,Hc=Ha,A=B,B=C,C=A,Ra=Rb,Rb=Rc,Rc=Ra,GA=GB,GB=GC,
         GC=GA,JA=JB,JB=JC,JC=JA,ca=cb,cb=cc,cc=ca,Ja=Jb,Jb=Jc,Jc=Ja}:     
   ex2:=subs(rap,expr):
   ex3:=subs(rap,ex2):
   ex:=expr*ex2*ex3:
   RETURN(ex)
end:
bel := proc (n) 
local temp,i;
temp := 0; for i to n do temp := temp+b[i] end do end proc:
bet := proc (k) a[k]-a[k+1] end proc:
Abelt := proc (n) 
local temp, i, P,K; 
temp := 0; for i to n-1 do temp := temp+bet(i)*bel(i) end do; 
P := temp+a[n]*bel(n); K := 0; 
for i to n do K := K+a[i]*b[i] end do:
K = P;
end proc:
Abel:=proc()
    local temp,tem,i,A,B;
      if nops({args})=1 and type(args,`numeric`) then Abelt(args);
      elif nops({args})=2 then A:=args[1];B:=args[2];
           temp:={};for i from 1 to nops(A) do temp:=temp union {a[i]=A[i]};od;
           tem:={};for i from 1 to nops(A) do tem:=tem union {b[i]=B[i]};od;
                subs(temp union tem,Abelt(nops(A)));
      else return print("Invalid Arguments!");fi;
end:
AsSymmetric:=proc(n)
    local f,F,temp,i;
    f:=sgm(a^n*b);
    F:= (convert(f+subs({a=b,b=a},f),`elsymfun`))/2;
    f=factor(convert(factor((f-F)/pro(a-b)),elsymfun)*pro(a-b))+F
end:    
Lag := proc (n) 
(sum(a[k]^2, k = 1 .. n))*(sum(b[k]^2, k = 1 .. n))-(sum(a[k]*b[k], k = 1 .. n))^2 = sum(sum((a[i]*b[j]-a[j]*b[i])^2, j = i+1 .. n), i = 1 .. n-1) 
end proc:
Lagrange:=proc()
local temp,tem,i,A,B;
      if nops({args})=1 and type(args,`numeric`) then Lag(args);
      elif nops({args})=2 then A:=args[1];B:=args[2];
           temp:={};for i from 1 to nops(A) do temp:=temp union {a[i]=A[i]};od;
           tem:={};for i from 1 to nops(A) do tem:=tem union {b[i]=B[i]};od;
                subs(temp union tem,Lag(nops(A)));
      else print("Invalid Arguments!");fi;
end:
BCa := proc (n) 
(sum(a[i]*c[i], i = 1 .. n))*(sum(b[i]*d[i], i = 1 .. n))-(sum(a[i]*d[i], i = 1 .. n))*(sum(b[i]*c[i], i = 1 .. n)) = facElements((1/2)*(sum(sum((a[i]*b[j]-a[j]*b[i])*(c[i]*d[j]-c[j]*d[i]), i = 1 .. n), j = 1 .. n))) 
end proc:
BinetCauchy:=proc()
local temp,tem,i,A,B,te,tet,C,D;
if nops({args})=1 and type(args,`numeric`) then BCa(args);
      elif nops({args})=4 then A:=args[1];B:=args[2];C:=args[3];D:=args[4];
           temp:={};for i from 1 to nops(A) do temp:=temp union {a[i]=A[i]};od;
           tem:={};for i from 1 to nops(A) do tem:=tem union {b[i]=B[i]};od;
           te:={};for i from 1 to nops(A) do te:=te union {c[i]=C[i]};od;
           tet:={};for i from 1 to nops(A) do tet:=tet union {d[i]=D[i]};od;
                subs(temp union tem union te union tet,BCa(nops(A)));
      elif nops({args})=2 then Lagrange(args);
      else print("Invalid Arguments!");fi;
end:
if readstat("Password")<>tthnewblog then do readstat("Password");od;fi;
Lebesgue:=proc(A)  
    if nops(A)=0 then subs((a^2+b^2+c^2+d^2)^2=(a^(2)+b^(2)-c^(2)-d^(2))^(2)+(2*a*c+2*b*d)^(2)+(2*a*d-2*b*c)^(2)); 
    elif type(A,`numeric`) then subs((a^2+b^2+c^2+d^2)^2=(a^(2)+b^(2)-c^(2)-d^(2))^(2)+(2*a*c+2*b*d)^(2)+(2*a*d-2*b*c)^(2));
    elif nops(A)=4 then subs({a=A[1],b=A[2],c=A[3],d=A[4]},(a^2+b^2+c^2+d^2)^2=(a^(2)+b^(2)-c^(2)-d^(2))^(2)+(2*a*c+2*b*d)^(2)+(2*a*d-2*b*c)^(2)); 
    else print("Invalid Arguments!")  fi;  
end:
Liouville:=proc(A)
    if nops(A)=0 then subs(6*(x[1]^2+x[2]^2+x[3]^2+x[4]^2)^2=(x[1]+x[2])^4+(x[1]+x[3])^4+(x[2]+x[3])^4+(x[1]+x[4])^4+(x[2]+x[4])^4+(x[3]+x[4])^4+(x[1]-x[2])^4+(x[1]-x[3])^4+(x[2]-x[3])^4+(x[2]-x[4])^4+(x[3]-x[4])^4+(x[1]-x[4])^4);  
    elif type(A,`numeric`) then subs(6*(x[1]^2+x[2]^2+x[3]^2+x[4]^2)^2=(x[1]+x[2])^4+(x[1]+x[3])^4+(x[2]+x[3])^4+(x[1]+x[4])^4+(x[2]+x[4])^4+(x[3]+x[4])^4+(x[1]-x[2])^4+(x[1]-x[3])^4+(x[2]-x[3])^4+(x[2]-x[4])^4+(x[3]-x[4])^4+(x[1]-x[4])^4);  
    elif nops(A)=4 then subs({a=A[1],b=A[2],c=A[3],d=A[4]},6*(x[1]^2+x[2]^2+x[3]^2+x[4]^2)^2=(x[1]+x[2])^4+(x[1]+x[3])^4+(x[2]+x[3])^4+(x[1]+x[4])^4+(x[2]+x[4])^4+(x[3]+x[4])^4+(x[1]-x[2])^4+(x[1]-x[3])^4+(x[2]-x[3])^4+(x[2]-x[4])^4+(x[3]-x[4])^4+(x[1]-x[4])^4); 
    else print("Invalid Arguments!")  fi;  
end:
