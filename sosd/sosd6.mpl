protect(a,b,c,d,e,ff);
sosd6:=proc(expr,x)
	local F,FF,sol;
	F:=a*x^5+x^6+b*x^4+c*x^3+d*x^2+e*x+ff;
     FF:=(1/4)*(2*x+a)^2*x^4-(1/4)*(a^2*x-4*b*x-2*c)^2*x^2/(a^2-4*b)+(1/4)*(2*a^2*d*x+a^2*e-8*b*d*x+2*c^2*x-4*b*e)^2/((a^2*d-4*b*d+c^2)*(a^2-4*b))+(1/4)*(4*a^2*d*ff-a^2*e^2-16*b*d*ff+4*b*e^2+4*c^2*ff)/(a^2*d-4*b*d+c^2);
	sol:=solve(identity(F=expr, x));
     if subs(sol,a^2-4*b)=0 then return print(`Can't not give SOS for it, you may try another tool.`);fi;
	if {sol}<>{} then return (subs(sol,FF));
	else return false;fi;
end:

#This is testing tool many inequality can not give SOS. Example:

f:=x^6-x^5-x^4+x^3+x^2+x+1;

sosd6(f);
