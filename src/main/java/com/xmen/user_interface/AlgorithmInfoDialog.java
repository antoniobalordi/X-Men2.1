package com.xmen.user_interface;

import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.StackPane;
import javafx.scene.layout.VBox;
import javafx.scene.paint.Color;
import javafx.stage.Modality;
import javafx.stage.Stage;

/**
 * Read-only modal that explains the Forget-mutation pipeline X-Men implements (Algorithm 1
 * of the companion paper). Wording is condensed from the project README so it stays in sync
 * with the published description.
 */
public final class AlgorithmInfoDialog {

  private AlgorithmInfoDialog() {}

  public static void show(Stage owner) {
    Stage stage = new Stage();
    stage.initOwner(owner);
    stage.initModality(Modality.APPLICATION_MODAL);
    stage.setTitle("How X-Men's Forget mutation works");

    Label title = new Label("How X-Men's Forget mutation works");
    title.getStyleClass().add("x-settings-title");

    Label sub = new Label(
        "A plain-English walkthrough of Algorithm 1 from the paper. The same nine steps "
            + "drive every Forget mutation X-Men generates.");
    sub.getStyleClass().add("x-settings-sub");
    sub.setWrapText(true);

    VBox steps = new VBox(14,
        step("1.", "Detect Forget(x) and ForgetRule(r)",
            "Scan the rule's action list for the lapse annotations. Forget(x): the human forgets "
                + "the message x (atomic forgetting). ForgetRule(r): the human forgets how to apply "
                + "the inference rule r, e.g. 'r_sdec' (procedural forgetting)."),
        step("2.", "Extract the agent's knowledge K",
            "Pull every term the agent has seen so far: the State the rule starts from, values "
                + "read from other premises, received messages and freshly generated values."),
        step("3.", "Update the Forget set and the forgotten rules, never K",
            "Add x to a separate Forget set and r to the set of forgotten rules. K never shrinks "
                + "(monotonic knowledge), so other occurrences of x in the model stay intact."),
        step("4.", "Look up the send target m₂",
            "Read the outgoing message the rule is about to send — the payload of Send/Out."),
        step("5.", "Ask: can m₂ still be derived?",
            "Run the Dolev-Yao derivation engine. If at least one derivation of m₂ avoids "
                + "every term blocked by the Forget set and every forgotten rule, the original "
                + "send stays unchanged."),
        step("6.", "Otherwise, find a type-compatible replacement",
            "Only for a forgotten message: search K for a candidate with the same format "
                + "(atom/pair/encrypt/function) and the same label as x. For passwords this "
                + "typically means: another password. A forgotten rule is never replaced."),
        step("7.", "Substitute x → replacement everywhere it appears in the rule",
            "Rewrite the Send action, the Out postcondition, and any witness action "
                + "(e.g. PasswordAttempt) so the trace truthfully records what the agent did. "
                + "State facts are left untouched — they still hold the original term plus the "
                + "replacement (knowledge stays monotonic)."),
        step("8.", "If no replacement exists → Skip; Neglect what can no longer be done",
            "Remove the send and its matching receive. In every case, Neglect removes the "
                + "internal actions (checks) the human can no longer perform because of the "
                + "lapse. The mutation produces a partial trace where the human could not proceed."),
        step("9.", "Emit a mutated .m file Tamarin can analyse",
            "Suffix the rule name with _M to make the mutation visible and write the new "
                + "theory to disk. The file is packaged in the response zip alongside the "
                + "(optional) derivation tree.")
    );

    ScrollPane scroll = new ScrollPane(steps);
    scroll.setFitToWidth(true);
    scroll.setStyle("-fx-background: transparent; -fx-background-color: transparent;");
    VBox.setVgrow(scroll, Priority.ALWAYS);

    Button close = new Button("Got it");
    close.getStyleClass().add("x-cta-primary");
    close.setOnAction(e -> stage.close());
    HBox closeRow = new HBox(close);
    closeRow.setAlignment(Pos.CENTER_RIGHT);

    VBox card = new VBox(16, title, sub, scroll, closeRow);
    card.getStyleClass().addAll("x-algo-panel");
    card.setPadding(new Insets(28));
    card.setPrefWidth(720);
    card.setPrefHeight(640);

    StackPane root = new StackPane(card);
    root.getStyleClass().add("x-root");
    root.setStyle(ThemedToast.transparentPopupStyleFrom(owner));

    Scene scene = new Scene(root);
    scene.setFill(Color.TRANSPARENT);
    scene.getStylesheets().add(
        AlgorithmInfoDialog.class.getResource("/css/main-v2.css").toExternalForm());
    stage.initStyle(javafx.stage.StageStyle.TRANSPARENT);
    stage.setScene(scene);
    stage.showAndWait();
  }

  private static HBox step(String number, String headline, String body) {
    Label num = new Label(number);
    num.setStyle("-fx-text-fill: -accent; -fx-font-size: 22px; -fx-font-weight: 800;");
    num.setMinWidth(32);

    Label h = new Label(headline);
    h.setStyle("-fx-text-fill: -text; -fx-font-size: 15px; -fx-font-weight: 700;");

    Label b = new Label(body);
    b.getStyleClass().add("x-algo-body");
    b.setWrapText(true);

    VBox text = new VBox(4, h, b);
    HBox.setHgrow(text, Priority.ALWAYS);
    return new HBox(12, num, text);
  }
}
