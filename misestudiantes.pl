def_type(grado, int).
def_type(estado, enum([inscripto, promueve, repite])).
def_type(rep, enum([alumnoEsGraduado, alumnoNoEsGraduado, alumnoNoEncontrado])).
def_type(inscripcion, [grado, estado]).
def_type(inscripciones, rel(alumno, inscripcion)).
def_type(alumnos, set(alumno)).

%%% -----------------------------------
%%% Los siguientes operadores fueron copiados de la librería de funciones parciales para
%%% agregar las declaraciones de tipos necesarias para usar el type checker
%%% -----------------------------------

dec_pp_type(inDom(X, rel(X,Y))).
inDom(Item, Rel) :- 
    dom(Rel, {Item/Z}) & dec(Z, set(X)).

dec_pp_type(ninDom(X, rel(X,Y))).
ninDom(Item, Rel) :- 
    dom(Rel, Z) & dec(Z, set(X)) & Item nin Z.

%%% -----------------------------------
%%% Parámetro utilizado para definición axiomática
%%% -----------------------------------
parameters([MaximoGrado]).

%%% -----------------------------------
%%% Variables de estado
%%% -----------------------------------
variables([Registrados, Inscripciones]).

%%% -----------------------------------
%%% Definición axiomática
%%% -----------------------------------
axiom(maximoGrado).
dec_p_type(maximoGrado(grado)).
maximoGrado(MaximoGrado) :- MaximoGrado = 12.

%%% -----------------------------------
%% Invariantes
%%% -----------------------------------
invariant(inscripcionesInv).
dec_p_type(inscripcionesInv(alumnos, inscripciones)).
inscripcionesInv(Registrados, Inscripciones) :-
    let([D],
        dom(Inscripciones, D) & dec(D, alumnos),
        D = Registrados
    ).

dec_p_type(n_inscripcionesInv(alumnos, inscripciones)).
n_inscripcionesInv(Registrados, Inscripciones) :-
    neg(let([D],
            dom(Inscripciones, D) & dec(D, alumnos),
            D = Registrados
    )).

invariant(maximoGradoInv).
dec_p_type(maximoGradoInv(alumnos, inscripciones)).
maximoGradoInv(Registrados, Inscripciones) :-
    foreach(A in Registrados,
            applyTo(Inscripciones, A, I) &
            dec(I, inscripcion) &
            [G, E] = I &
            dec(G, grado) &
            dec(E, estado) &
            maximoGrado(MaximoGrado) &
            dec(MaximoGrado, grado) &
            G =< MaximoGrado).

dec_p_type(n_maximoGradoInv(alumnos, inscripciones)).
n_maximoGradoInv(Registrados, Inscripciones) :-
    exists(A in Registrados,
             applyTo(Inscripciones, A, I) &
             dec(I, inscripcion) &
             [G, E] = I &
             dec(G, grado) &
             dec(E, estado) &
             maximoGrado(MaximoGrado) &
             dec(MaximoGrado, grado) &
             G > MaximoGrado).

invariant(inscripcionesPfunInv).
dec_p_type(inscripcionesPfunInv(inscripciones)).
inscripcionesPfunInv(Inscripciones) :-
    pfun(Inscripciones).

dec_p_type(n_inscripcionesPfunInv(inscripciones)).
n_inscripcionesPfunInv(Inscripciones) :-
    npfun(Inscripciones).

%%% -----------------------------------
%%% Estado inicial
%%% -----------------------------------
dec_p_type(misEstudiantesInicial(alumnos, inscripciones)).
initial(misEstudiantesInicial).
misEstudiantesInicial(Registrados, Inscripciones) :-
    Registrados = {} &
    Inscripciones = {}.

%%% -----------------------------------
%%% Operaciones
%%% -----------------------------------
dec_p_type(inscribirAlumnoOk(alumnos, inscripciones, alumno, alumnos, inscripciones)).
inscribirAlumnoOk(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) :-
    Alumno nin Registrados &
    un(Inscripciones, {[Alumno, [1, inscripto]]} , Inscripciones_) &
    un(Registrados, {Alumno}, Registrados_).

dec_p_type(inscribirAlumnoRegistradoE(alumnos, inscripciones, alumno, alumnos, inscripciones)).
inscribirAlumnoRegistradoE(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) :-
    Alumno in Registrados &
    Inscripciones_ = Inscripciones &
    Registrados_ = Registrados.

operation(inscribirAlumno).
dec_p_type(inscribirAlumno(alumnos, inscripciones, alumno, alumnos, inscripciones)).
inscribirAlumno(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) :-
    inscribirAlumnoOk(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) or
    inscribirAlumnoRegistradoE(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_).

dec_p_type(reinscribirAlumnoPromovidoOk(alumnos, inscripciones, alumno, alumnos, inscripciones)).
reinscribirAlumnoPromovidoOk(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) :-
    Alumno in Registrados &
    applyTo(Inscripciones, Alumno, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    maximoGrado(MaximoGrado) &
    dec(MaximoGrado, grado) &
    G < MaximoGrado &
    E = promueve &
    G_ is G + 1 &
    dec(G_, grado) &
    I_ = [G_, inscripto] &
    dec(I_, inscripcion) &
    oplus(Inscripciones, {[Alumno, I_]}, Inscripciones_) &
    Registrados_ = Registrados.

dec_p_type(reinscribirAlumnoRepitenteOk(alumnos, inscripciones, alumno, alumnos, inscripciones)).
reinscribirAlumnoRepitenteOk(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) :-
    Alumno in Registrados &
    applyTo(Inscripciones, Alumno, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    maximoGrado(MaximoGrado) &
    dec(MaximoGrado, grado) &
    G =< MaximoGrado &
    E = repite &
    I_ = [G, inscripto] &
    dec(I_, inscripcion) &
    oplus(Inscripciones, {[Alumno, I_]}, Inscripciones_) &
    Registrados_ = Registrados.

dec_p_type(reinscribirAlumnoNoEncontradoE(alumnos, inscripciones, alumno, alumnos, inscripciones)).
reinscribirAlumnoNoEncontradoE(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) :-
    Alumno nin Registrados &
    Inscripciones_ = Inscripciones &
    Registrados_ = Registrados.

dec_p_type(reinscribirAlumnoGraduadoE(alumnos, inscripciones, alumno, alumnos, inscripciones)).
reinscribirAlumnoGraduadoE(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) :-
    Alumno in Registrados &
    applyTo(Inscripciones, Alumno, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    maximoGrado(MaximoGrado) &
    dec(MaximoGrado, grado) &
    G = MaximoGrado &
    E = promueve &
    Inscripciones_ = Inscripciones &
    Registrados_ = Registrados.

dec_p_type(reinscribirAlumnoDobleInscripE(alumnos, inscripciones, alumno, alumnos, inscripciones)).
reinscribirAlumnoDobleInscripE(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) :-
    Alumno in Registrados &
    applyTo(Inscripciones, Alumno, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    E = inscripto &
    Inscripciones_ = Inscripciones &
    Registrados_ = Registrados.

operation(reinscribirAlumno).
dec_p_type(reinscribirAlumno(alumnos, inscripciones, alumno, alumnos, inscripciones)).
reinscribirAlumno(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) :-
    reinscribirAlumnoPromovidoOk(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) or
    reinscribirAlumnoRepitenteOk(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) or
    reinscribirAlumnoNoEncontradoE(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) or
    reinscribirAlumnoGraduadoE(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) or
    reinscribirAlumnoDobleInscripE(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_).

dec_p_type(cerrarInscripcionOk(alumnos, inscripciones, alumno, estado, alumnos, inscripciones)).
cerrarInscripcionOk(Registrados, Inscripciones, Alumno, Estado, Registrados_, Inscripciones_) :-
    Alumno in Registrados &
    Estado neq inscripto &
    applyTo(Inscripciones, Alumno, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    I_ = [G, Estado] &
    dec(I_, inscripcion) &
    oplus(Inscripciones, {[Alumno, I_]}, Inscripciones_) &
    Registrados_ = Registrados.

dec_p_type(cerrarInscripcionEstadoInvalidoE(alumnos, inscripciones, estado, alumnos, inscripciones)).
cerrarInscripcionEstadoInvalidoE(Registrados, Inscripciones, Estado, Registrados_, Inscripciones_) :-
    Estado = inscripto &
    Inscripciones_ = Inscripciones &
    Registrados_ = Registrados.

dec_p_type(cerrarInscripcionAlumnoNoEncontradoE(alumnos, inscripciones, alumno, alumnos, inscripciones)).
cerrarInscripcionAlumnoNoEncontradoE(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_) :-
    Alumno nin Registrados &
    Inscripciones_ = Inscripciones &
    Registrados_ = Registrados.

operation(cerrarInscripcion).
dec_p_type(cerrarInscripcion(alumnos, inscripciones, alumno, estado, alumnos, inscripciones)).
cerrarInscripcion(Registrados, Inscripciones, Alumno, Estado, Registrados_, Inscripciones_) :-
    cerrarInscripcionOk(Registrados, Inscripciones, Alumno, Estado, Registrados_, Inscripciones_) or
    cerrarInscripcionEstadoInvalidoE(Registrados, Inscripciones, Estado, Registrados_, Inscripciones_) or
    cerrarInscripcionAlumnoNoEncontradoE(Registrados, Inscripciones, Alumno, Registrados_, Inscripciones_).

dec_p_type(alumnoEsGraduadoSiOk(alumnos, inscripciones, alumno, rep, alumnos, inscripciones)).
alumnoEsGraduadoSiOk(Registrados, Inscripciones, Alumno, Rep, Registrados, Inscripciones) :-
    Alumno in Registrados &
    applyTo(Inscripciones, Alumno, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    maximoGrado(MaximoGrado) &
    dec(MaximoGrado, grado) &
    G = MaximoGrado &
    E = promueve &
    Rep = alumnoEsGraduado.

dec_p_type(alumnoEsGraduadoNoOk(alumnos, inscripciones, alumno, rep, alumnos, inscripciones)).
alumnoEsGraduadoNoOk(Registrados, Inscripciones, Alumno, Rep, Registrados, Inscripciones) :-
    Alumno in Registrados &
    applyTo(Inscripciones, Alumno, I) &
    dec(I, inscripcion) &
    [G, E] = I &
    dec(G, grado) &
    dec(E, estado) &
    maximoGrado(MaximoGrado) &
    dec(MaximoGrado, grado) &
    (G neq MaximoGrado or E neq promueve) &
    Rep = alumnoNoEsGraduado.

dec_p_type(alumnoEsGraduadoNoEncontradoE(alumnos, inscripciones, alumno, rep, alumnos, inscripciones)).
alumnoEsGraduadoNoEncontradoE(Registrados, Inscripciones, Alumno, Rep, Registrados, Inscripciones) :-
    Alumno nin Registrados &
    Rep = alumnoNoEncontrado.

dec_p_type(alumnoEsGraduado(alumnos, inscripciones, alumno, rep, alumnos, inscripciones)).
operation(alumnoEsGraduado).
alumnoEsGraduado(Registrados, Inscripciones, Alumno, Rep, Registrados, Inscripciones) :-
    alumnoEsGraduadoSiOk(Registrados, Inscripciones, Alumno, Rep, Registrados, Inscripciones) or
    alumnoEsGraduadoNoOk(Registrados, Inscripciones, Alumno, Rep, Registrados, Inscripciones) or
    alumnoEsGraduadoNoEncontradoE(Registrados, Inscripciones, Alumno, Rep, Registrados, Inscripciones).
