% Verification conditions for misestudiantes.pl

% Run check_vcs_misestudiantes to see if the program verifies all the VCs

:- notype_check.

:- consult('misestudiantes.pl').

:- prolog_call((
    retractall(all_unsat_vc(_,_,_,_,_,_)),
    retractall(dinvariant(_,_,_)),
    retractall(daxiom(_,_,_)),
    (exists_file('misestudiantes-all.pl') ->
       open('misestudiantes-all.pl',read,StreamVC)
    ;
       print_notfile('misestudiantes-all.pl')
    ),
    style_check(-singleton),
    setlog:consult_vc(StreamVC),
    style_check(+singleton),
    close(StreamVC))).

% Change this number for a different timeout (ms)
def_to(60000).

:- prolog_call(nb_setval(vc_num,0)).
:- prolog_call(nb_setval(vc_ok,0)).
:- prolog_call(nb_setval(vc_err,0)).
:- prolog_call(nb_setval(vc_to,0)).
:- prolog_call(nb_setval(vc_time,0)).

:- prolog_call(dynamic(unsat_sol/6)).
:- prolog_call(dynamic(vc_proved/1)).

axioms_sat :-
  maximoGrado(MaximoGrado).

misEstudiantesInicial_sat_inscripcionesInv :-
  misEstudiantesInicial(Registrados,Inscripciones) &
  inscripcionesInv(Registrados,Inscripciones).

misEstudiantesInicial_sat_maximoGradoInv :-
  misEstudiantesInicial(Registrados,Inscripciones) &
  maximoGradoInv(Registrados,Inscripciones).

misEstudiantesInicial_sat_inscripcionesPfunInv :-
  misEstudiantesInicial(Registrados,Inscripciones) &
  inscripcionesPfunInv(Inscripciones).

inscribirAlumno_is_sat :-
  inscribirAlumno(Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) & 
  delay([Registrados,Inscripciones] neq [Registrados_,Inscripciones_],false).

inscribirAlumno_pi_inscripcionesInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inscripcionesInv(Registrados,Inscripciones) &
    inscribirAlumno(Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) implies
    inscripcionesInv(Registrados_,Inscripciones_)
  ).

inscribirAlumno_pi_maximoGradoInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    maximoGradoInv(Registrados,Inscripciones) &
    inscribirAlumno(Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) implies
    maximoGradoInv(Registrados_,Inscripciones_)
  ).

inscribirAlumno_pi_inscripcionesPfunInv(Inscripciones,Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  inscripcionesInv(Registrados, Inscripciones) &
  neg(
    inscripcionesPfunInv(Inscripciones) &
    inscribirAlumno(Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) implies
    inscripcionesPfunInv(Inscripciones_)
  ).

reinscribirAlumno_is_sat :-
  reinscribirAlumno(Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) & 
  delay([Registrados,Inscripciones] neq [Registrados_,Inscripciones_],false).

reinscribirAlumno_pi_inscripcionesInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inscripcionesInv(Registrados,Inscripciones) &
    reinscribirAlumno(Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) implies
    inscripcionesInv(Registrados_,Inscripciones_)
  ).

reinscribirAlumno_pi_maximoGradoInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    maximoGradoInv(Registrados,Inscripciones) &
    reinscribirAlumno(Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) implies
    maximoGradoInv(Registrados_,Inscripciones_)
  ).

reinscribirAlumno_pi_inscripcionesPfunInv(Inscripciones,Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inscripcionesPfunInv(Inscripciones) &
    reinscribirAlumno(Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_) implies
    inscripcionesPfunInv(Inscripciones_)
  ).

cerrarInscripcion_is_sat :-
  cerrarInscripcion(Registrados,Inscripciones,Alumno,Estado,Registrados_,Inscripciones_) & 
  delay([Registrados,Inscripciones] neq [Registrados_,Inscripciones_],false).

cerrarInscripcion_pi_inscripcionesInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Estado,Registrados_,Inscripciones_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inscripcionesInv(Registrados,Inscripciones) &
    cerrarInscripcion(Registrados,Inscripciones,Alumno,Estado,Registrados_,Inscripciones_) implies
    inscripcionesInv(Registrados_,Inscripciones_)
  ).

cerrarInscripcion_pi_maximoGradoInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Estado,Registrados_,Inscripciones_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    maximoGradoInv(Registrados,Inscripciones) &
    cerrarInscripcion(Registrados,Inscripciones,Alumno,Estado,Registrados_,Inscripciones_) implies
    maximoGradoInv(Registrados_,Inscripciones_)
  ).

cerrarInscripcion_pi_inscripcionesPfunInv(Inscripciones,Registrados,Inscripciones,Alumno,Estado,Registrados_,Inscripciones_) :-
  % here conjoin other ax/inv as hypotheses if necessary
  neg(
    inscripcionesPfunInv(Inscripciones) &
    cerrarInscripcion(Registrados,Inscripciones,Alumno,Estado,Registrados_,Inscripciones_) implies
    inscripcionesPfunInv(Inscripciones_)
  ).

alumnoEsGraduado_is_sat :-
  alumnoEsGraduado(Registrados,Inscripciones,Alumno,Rep,Registrados,Inscripciones).

alumnoEsGraduado_pi_inscripcionesInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Rep,Registrados,Inscripciones):-
  % alumnoEsGraduado doesn't change inscripcionesInv variables
  neg(true).

alumnoEsGraduado_pi_maximoGradoInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Rep,Registrados,Inscripciones):-
  % alumnoEsGraduado doesn't change maximoGradoInv variables
  neg(true).

alumnoEsGraduado_pi_inscripcionesPfunInv(Inscripciones,Registrados,Inscripciones,Alumno,Rep,Registrados,Inscripciones):-
  % alumnoEsGraduado doesn't change inscripcionesPfunInv variables
  neg(true).

update_time(Tf,Ti) :-
  prolog_call(
    (nb_getval(vc_time,VCT),
     VCT_ is VCT + Tf - Ti,
     nb_setval(vc_time,VCT_)
    )
  ).

update_count(C) :-
  prolog_call(
    (nb_getval(C,VCN),
     VCN_ is VCN + 1,
     nb_setval(C,VCN_)
    )
  ).

check_sat_vc(VCID) :-
  prolog_call((setlog:vc_proved(VCID) -> R = proved ; R = unproved)) &
  (R == unproved &
   write('\nChecking ') & write(VCID) & write(' ... ') &
   update_count(vc_num) &
   ((prolog_call(setlog(VCID)) &
    update_count(vc_ok) &
    prolog_call(assertz(vc_proved(VCID))) &
    write_ok)!
    or
    update_count(vc_err) &
    write_err
   )
   or
   R == proved
  ).

check_unsat_vc(VCID,TO,Opt) :-
  prolog_call(
    (VCID =.. [H | _],
     (\+setlog:vc_proved(H) ->
        setlog:all_unsat_vc(H,T,ID,VC,Op,VN),
        copy_term([VC,VN],[VCC,VNC]),
        write('\nChecking '), write(H), write(' ... '), flush_output,
        setlog(update_count(vc_num)),
        get_time(Ti),
        rsetlog(VC,TO,Cons,Res,Opt),
        get_time(Tf)
     ;
        Res = proved
     )
    )
  ) &
  ((Res = failure)! &
    update_count(vc_ok) &
    update_time(Tf,Ti) &
    prolog_call((retractall(setlog:unsat_sol(_,H,_,_,_,_)),
                 assertz(vc_proved(H)))) &
    write_ok
  or
   (Res = timeout)! &
    update_count(vc_to) &
    write_to
  or
    (Res = proved)!
  or
    update_count(vc_err) &
    prolog_call((term_string(VCC,VCS,[variable_names(VNC)]),
                 rsetlog_str(VCS,VNC,TO,_,_,[groundsol]))) &
    prolog_call((retractall(setlog:unsat_sol(_,H,_,_,_,_)),
                 assertz(unsat_sol(T,H,ID,Cons,VN,VNC)))) &
    write_err
  ).

write_ok :-
  prolog_call(ansi_format([bold,fg(green)],'OK',[])).

write_to :-
  prolog_call(ansi_format([bold,fg(255,255,50)],'TIMEOUT',[])).

write_err :-
  prolog_call(ansi_format([bold,fg(red)],'ERROR',[])).

check_vcs_misestudiantes :-
   def_to(TO) &
   prolog_call(setlog(check_aux(TO,[])!)).

check_vcs_misestudiantes(Opt) :-
   def_to(TO) &
   prolog_call(setlog(check_aux(TO,Opt)!)).

check_vcs_misestudiantes(TO,Opt) :-
   prolog_call(setlog(check_aux(TO,Opt)!)).

check_aux(TO,Opt) :-
  prolog_call(
    (retractall(unsat_sol(_,_,_,_,_,_)),
     nb_setval(vc_num,0),
     nb_setval(vc_time,0),
     nb_setval(vc_ok,0),
     nb_setval(vc_err,0),
     nb_setval(vc_to,0)
    )
  ) &
  check_sat_vc(axioms_sat) &
  check_sat_vc(misEstudiantesInicial_sat_inscripcionesInv) &
  check_sat_vc(misEstudiantesInicial_sat_maximoGradoInv) &
  check_sat_vc(misEstudiantesInicial_sat_inscripcionesPfunInv) &
  check_sat_vc(inscribirAlumno_is_sat) &
  check_sat_vc(reinscribirAlumno_is_sat) &
  check_sat_vc(cerrarInscripcion_is_sat) &
  check_sat_vc(alumnoEsGraduado_is_sat) &
  check_unsat_vc(inscribirAlumno_pi_inscripcionesInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_),TO,Opt) &
  check_unsat_vc(inscribirAlumno_pi_maximoGradoInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_),TO,Opt) &
  check_unsat_vc(inscribirAlumno_pi_inscripcionesPfunInv(Inscripciones,Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_),TO,Opt) &
  check_unsat_vc(reinscribirAlumno_pi_inscripcionesInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_),TO,Opt) &
  check_unsat_vc(reinscribirAlumno_pi_maximoGradoInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_),TO,Opt) &
  check_unsat_vc(reinscribirAlumno_pi_inscripcionesPfunInv(Inscripciones,Registrados,Inscripciones,Alumno,Registrados_,Inscripciones_),TO,Opt) &
  check_unsat_vc(cerrarInscripcion_pi_inscripcionesInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Estado,Registrados_,Inscripciones_),TO,Opt) &
  check_unsat_vc(cerrarInscripcion_pi_maximoGradoInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Estado,Registrados_,Inscripciones_),TO,Opt) &
  check_unsat_vc(cerrarInscripcion_pi_inscripcionesPfunInv(Inscripciones,Registrados,Inscripciones,Alumno,Estado,Registrados_,Inscripciones_),TO,Opt) &
  check_unsat_vc(alumnoEsGraduado_pi_inscripcionesInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Rep,Registrados,Inscripciones),TO,Opt) &
  check_unsat_vc(alumnoEsGraduado_pi_maximoGradoInv(Registrados,Inscripciones,Registrados,Inscripciones,Alumno,Rep,Registrados,Inscripciones),TO,Opt) &
  check_unsat_vc(alumnoEsGraduado_pi_inscripcionesPfunInv(Inscripciones,Registrados,Inscripciones,Alumno,Rep,Registrados,Inscripciones),TO,Opt) &
  prolog_call(
    (nb_getval(vc_num,VCN),
     nb_getval(vc_time,VCT),
     nb_getval(vc_ok,VCOK),
     nb_getval(vc_err,VCE),
     nb_getval(vc_to,VCTO)
    )
  ) &
  nl & nl &
  write("Total VCs: ") & write(VCN) &
  write(" (discharged: ") & write(VCOK) &
  write(", failed: ") & write(VCE) &
  write(", timeout: ") & write(VCTO) & write(")") & nl &
  write("Execution time (discharged): ") & write(VCT) & write(" s").

:- nl & prolog_call(ansi_format([bold,fg(green)],'Type checking has been deactivated.',[])) & nl & nl.

:- nl & prolog_call(ansi_format([bold,fg(green)],'Call check_vcs_misestudiantes to run the verification conditions.',[])) & nl & nl.

