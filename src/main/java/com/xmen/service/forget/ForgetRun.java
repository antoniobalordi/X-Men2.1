package com.xmen.service.forget;

import com.xmen.model.Rule;
import java.util.ArrayList;

/**
 * One execution of the ceremony after the first lapse: the specification mutated so far and the
 * human's Forget context (K, Forget, R̄). Algorithm 1 is applied to every later human transition
 * of the run, so lapses persist and their effects accumulate in {@code theory}. A REPLACE with
 * several variants branches the run.
 */
public record ForgetRun(ArrayList<Rule> theory, ForgetContext ctx) {}
