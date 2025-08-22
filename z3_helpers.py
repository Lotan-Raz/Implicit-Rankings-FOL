from collections.abc import Iterable

import z3

type ResultPair = tuple[z3.CheckSatResult, z3.ModelRef | None]


def sat_check(
    constraints: Iterable[z3.BoolRef],
    *,
    find_model: bool = True,
    minimize_model: bool = True,
    unsat_core: bool = False,
    print_calls: bool = False,
    print_smtlib: bool = False,
    minimize_sorts: tuple[z3.SortRef, ...] = (),
) -> ResultPair:
    z3.set_param("timeout", 5 * 60 * 1000)  # 5 minute timeout
    solver = z3.Solver()
    solver.set(mbqi=True)
    # Enable unsat core tracking
    if unsat_core:
        solver.set(unsat_core=True)
        for i, c in enumerate(constraints):
            if print_calls:
                print("constraint number", i)
                print(c)
            solver.assert_and_track(c, str(i))
    else:
        for c in constraints:
            if print_calls:
                print(c)
            solver.add(c)

    if print_smtlib:
        print(solver.sexpr())  # printing to smtlib

    result = solver.check()
    if result == z3.unsat:
        if unsat_core:
            core = solver.unsat_core()
            print("Unsat core:", core)
    if result == z3.sat:
        model = None
        if find_model:
            try:
                full_model = solver.model()
            except z3.Z3Exception as e:
                print(f"sat but no model: {e}")
            if minimize_model:
                for size in range(1, 8):
                    solver.push()
                    for sort in minimize_sorts:
                        solver.add(size_constraint(sort, size))
                        new_result = solver.check()
                        if new_result == z3.sat:
                            print(f"small model of size: {size}")
                            model = solver.model()
                            break
                        else:
                            solver.pop()

            if model is None:
                print("small model failed")
                model = full_model

        return z3.sat, model
    else:
        return result, None


def print_model_in_order(
    model: ResultPair | z3.ModelRef | None,
    symbols: Iterable[z3.FuncDeclRef],
    print_model_to_file: bool = True,
):
    if isinstance(model, tuple):
        model = model[1]
    if model is None:
        return
    sorts = model.sorts()
    for s in sorts:
        print(model.get_universe(s))
    try:
        for symbol in symbols:
            print(symbol, ":", model[symbol])  # type: ignore
    except Exception as e:
        print("A KeyError occurred:", e)
        print(model)
    if print_model_to_file:
        with open("model.txt", "w") as f:
            try:
                for symbol in symbols:
                    f.write(str(symbol) + " : " + str(model[symbol]) + "\n")  # type: ignore
            except Exception as e:
                print("An error occurred while writing the model to file:", e)
                f.write(str(model))


def size_constraint(sort: z3.SortRef, size: int):
    each = z3.Const(f"{sort}_each", sort)
    return z3.ForAll(
        each,
        z3.Or(*((each == z3.Const(f"{sort}_size_{i}", sort)) for i in range(size))),
    )
