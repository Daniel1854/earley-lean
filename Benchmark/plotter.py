"""
Desired plots: (x: num_chars (log), y: runtime in ms (log)?)
- Comparison plot of each grammar for the scala-variants and lean
- Comparison plot of the grammars for lean
- Comparison plot of the binsizes for each grammar
"""

import argparse

import pandas
from matplotlib import pyplot as plt
from enum import Enum
from dataclasses import dataclass
from typing import Optional


class Mode(Enum):
    GRAMMAR = "grammar"  # plot all variants for a given grammar
    GRAMMAR_NAIVE = "grammar_naive"  # plot the naive variants for a given grammar
    GRAMMAR_OPT = "grammar_opt"  # plot the opt variants for a given grammar
    COMP = "comp"  # plot all grammars for lean
    SIZES = "sizes"  # plot binsizes for each grammar


GRAMMAR_MODES = [Mode.GRAMMAR, Mode.GRAMMAR_NAIVE, Mode.GRAMMAR_OPT]


class Grammar(Enum):
    ONE = "1"
    TWO = "2"
    THREE = "3"
    FOUR = "4"
    FIVE = "5"


def grammar_to_bnf(grammar: Grammar) -> str:
    match grammar:
        case Grammar.ONE:
            return "S → SS | a"
        case Grammar.TWO:
            return "S → aS | a"
        case Grammar.THREE:
            return "S → aSa | a"
        case Grammar.FOUR:
            return "S → Sa | a"
        case Grammar.FIVE:
            return "S → SX | a\n X → Y | Z\n Y → a\n Z → a"


class Variant(Enum):
    LEAN_NAIVE = "lean-naive"  # lean with naive algorithm
    LEAN_OPT = "lean-opt"  # lean with caches, but no pointer maintenance
    LEAN_ITEM_POINTERS = "lean-item-pointers"  # lean with only the itemcache
    LEAN_OPT_POINTERS = "lean-opt-pointers"  # lean with caches
    ISABELLE = "isabelle"  # exported isabelle code
    SCALA_NAIVE = "scala-naive"  # isabelle code handwritten in scala
    SCALA_OPT = "scala-opt"  # optimized scala implementation without maintaining pointerinformation


@dataclass
class Experiment:
    variant: Variant
    grammar: Grammar

    def to_filename(self):
        postfix = f"grammar={self.grammar.value}_variant={self.variant.value}.csv"
        if self.variant in [
            Variant.LEAN_NAIVE,
            Variant.LEAN_OPT,
            Variant.LEAN_ITEM_POINTERS,
            Variant.LEAN_OPT_POINTERS,
        ]:
            return f"lean/lean_{postfix}"
        else:
            return f"scala/scala_{postfix}"


def plot(mode: Mode, grammar: Optional[Grammar]):
    fig, ax = plt.subplots()
    if mode is Mode.GRAMMAR:
        assert (
            grammar is not None
        ), "Called plot with grammar mode, but didnt supply a grammar!"
        experiments = [
            Experiment(variant=variant, grammar=grammar) for variant in Variant
        ]
    elif mode is Mode.GRAMMAR_NAIVE:
        assert (
            grammar is not None
        ), "Called plot with grammar mode, but didnt supply a grammar!"
        if grammar in [Grammar.ONE, Grammar.TWO, Grammar.THREE]:
            variants = [Variant.ISABELLE, Variant.SCALA_NAIVE, Variant.LEAN_NAIVE]
        else:
            variants = [Variant.ISABELLE, Variant.SCALA_NAIVE]
        experiments = [
            Experiment(variant=variant, grammar=grammar) for variant in variants
        ]
    elif mode is Mode.GRAMMAR_OPT:
        assert (
            grammar is not None
        ), "Called plot with grammar mode, but didnt supply a grammar!"
        if grammar in [Grammar.ONE, Grammar.TWO, Grammar.THREE]:
            variants = [
                Variant.LEAN_OPT,
                Variant.LEAN_ITEM_POINTERS,
                Variant.LEAN_OPT_POINTERS,
                Variant.SCALA_OPT,
            ]
        else:
            variants = [
                Variant.LEAN_OPT,
                Variant.LEAN_NAIVE,
                Variant.LEAN_ITEM_POINTERS,
                Variant.LEAN_OPT_POINTERS,
                Variant.SCALA_OPT,
            ]
        experiments = [
            Experiment(variant=variant, grammar=grammar) for variant in variants
        ]
    else:
        variant = Variant.LEAN_OPT_POINTERS
        experiments = [
            Experiment(variant=variant, grammar=grammar) for grammar in Grammar
        ]

    for idx, experiment in enumerate(experiments):
        df = pandas.read_csv(experiment.to_filename())
        n = df["num_chars"].values
        if mode is Mode.SIZES:
            y = df["num_bins"].values
        else:
            # y = df["num_miliseconds"].map(lambda x: x / 1000).values
            y = df["num_miliseconds"].values
        if mode in GRAMMAR_MODES:
            label = f"{experiment.variant.value}"
        else:
            label = f"{grammar_to_bnf(experiment.grammar)}"
        if idx == 0:
            marker = "x"
        elif idx == 1:
            marker = "^"
        elif idx == 2:
            marker = "o"
        elif idx == 3:
            marker = "s"
        elif idx == 4:
            marker = "v"
        elif idx == 5:
            marker = "D"
        elif idx == 6:
            marker = "<"
        else:
            assert False, "controlflow issue"

        ax.plot(n, y, marker=marker, fillstyle="none", label=label)

    ax.grid(True, linestyle="--")

    ax.set_xlabel("Input length")
    if mode is Mode.SIZES:
        ax.set_ylabel("Total Size of the Bins")
        ax.set_xscale("log")
        ax.set_yscale("log")
        ax.legend(loc="lower right")
    elif mode in [Mode.GRAMMAR_NAIVE, Mode.GRAMMAR_OPT]:
        ax.set_ylabel("Duration [ms]")
        ax.legend(loc="lower right")
    else:
        ax.set_xscale("log")
        # ax.set_xlim(xmin=10, xmax=100_000)
        ax.set_yscale("log")
        ax.set_ylim(ymin=1, ymax=100_000)
        ax.set_ylabel("Duration [ms]")
        ax.legend(loc="upper left")

    # ax.legend(loc="center right")
    # ax.legend(loc="upper left", bbox_to_anchor=(1, 1))
    # plt.tight_layout()

    if mode in GRAMMAR_MODES:
        if mode is Mode.GRAMMAR_NAIVE:
            prefix = "naive_"
        elif mode is Mode.GRAMMAR_OPT:
            prefix = "opt_"
        else:
            prefix = ""
        ax.set_title(f"Runtime of '{grammar_to_bnf(grammar).replace('\n', ',')}'")
        fig.savefig(f"{prefix}grammar={grammar.value}.svg", bbox_inches="tight")
    elif mode is Mode.COMP:
        ax.set_title(f"Runtime of '{variant.value}'")
        fig.savefig(f"comp_{variant.value}.svg", bbox_inches="tight")
    elif mode is Mode.SIZES:
        ax.set_title(f"Total size of the bins for '{variant.value}'")
        fig.savefig(f"sizes_{variant.value}.svg", bbox_inches="tight")
    plt.close()


def main():
    parser = argparse.ArgumentParser(description="Plot some measurements")
    parser.add_argument(
        "-g",
        "--grammar",
        help="which grammar to plot",
    )
    parser.add_argument(
        "-m",
        "--mode",
        type=Mode,
        choices=list(Mode),
        help="Lowercase!",
        required=True,
    )
    args = parser.parse_args()
    mode = Mode(args.mode)
    grammar = Grammar(args.grammar) if mode in GRAMMAR_MODES else None
    plot(mode, grammar)


if __name__ == "__main__":
    main()
