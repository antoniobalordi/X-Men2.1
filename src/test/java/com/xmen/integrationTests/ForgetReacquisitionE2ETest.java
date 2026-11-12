package com.xmen.integrationTests;

import static com.xmen.integrationTests.ForgetEndpointHarness.ruleText;
import static org.assertj.core.api.Assertions.assertThat;

import com.xmen.config.CeremonyVocabulary;
import com.xmen.service.impl.ForgetMutationStrategy;
import com.xmen.utilities.MutationWorkspace;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;
import java.util.stream.Stream;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.test.context.ActiveProfiles;
import org.springframework.test.web.servlet.setup.MockMvcBuilders;
import org.springframework.web.context.WebApplicationContext;

/**
 * Re-acquisition (Example 3; pp. 15 and 17 of the journal manuscript): a forgotten message becomes
 * usable again when the human receives it again. The send of the transition that receives it, and
 * every later send, are then preserved. Each test has a control in which the value is not received
 * again, so the lapse persists.
 *
 * <p>In both models the lapse at User_1 does not affect User_1's own send, so nothing is replaced or
 * propagated before User_2 receives pw1 again.
 */
@SpringBootTest
@ActiveProfiles("test")
@DisplayName("Forget: a forgotten message received again is usable again")
class ForgetReacquisitionE2ETest {

  private static final String FORGET = "/api/forget/mutations";

  /**
   * Case (2): the user knows pw1 from the setup and forgets it at User_1. The server then sends pw1
   * (a reminder), which User_2 receives; User_2 and User_3 send messages built from pw1.
   */
  private static final String CASE2 = """
      /****MODEL****/
      theory ReacquisitionCase2

      begin

      builtins: symmetric-encryption

      /****RULES****/

      rule humansetup:
      	[ Fr(~k), Fr(~pw1), Fr(~pw2) ]
      	--[ OnlyOnce() ]->
      	[ !Type($User,'key',~k)
      	, !Type($User,'password',~pw1)
      	, !Type($User,'password',~pw2)
      	, !Init($User,$Server,~k,~pw1,~pw2)
      	]

      rule Setup:
      	[ !Init($User,$Server,k,pw1,pw2) ]
      	--[ Setup($User), Roles($User,$Server) ]->
      	[ State($User,'1',<$Server,k,pw1,pw2>), State($Server,'1',<$User,k,pw1>) ]

      rule Server_1:
      	[ State($Server,'1',<$User,k,pw1>) ]
      	--[ Hello($Server) ]->
      	[ State($Server,'2',<$User,k,pw1>), Out('hello') ]

      rule User_1:
      	[ State($User,'1',<$Server,k,pw1,pw2>), In('hello') ]
      	--[ H(), Receive($User,'c1','hello'), Forget(pw1), Send($User,'m1',senc('hi',k)), To($Server) ]->
      	[ State($User,'2',<$Server,k,pw1,pw2>), Out(senc('hi',k)) ]

      rule Server_2:
      	[ State($Server,'2',<$User,k,pw1>), In(senc('hi',k)) ]
      	--[ Hi($Server) ]->
      	[ State($Server,'3',<$User,k,pw1>), Out(pw1) ]

      rule User_2:
      	[ State($User,'2',<$Server,k,pw1,pw2>), In(pw1) ]
      	--[ H(), Receive($User,'c2',pw1), Send($User,'m2',senc(<'ack',pw1>,k)), To($Server) ]->
      	[ State($User,'3',<$Server,k,pw1,pw2>), Out(senc(<'ack',pw1>,k)) ]

      rule Server_3:
      	[ State($Server,'3',<$User,k,pw1>), In(senc(<'ack',x>,k)) ]
      	--[ Ack($Server,x) ]->
      	[ State($Server,'4',<$User,k,pw1>), Out('ok') ]

      rule User_3:
      	[ State($User,'3',<$Server,k,pw1,pw2>), In('ok') ]
      	--[ H(), Receive($User,'c3','ok'), Send($User,'m3',senc(pw1,k)), To($Server) ]->
      	[ State($User,'4',<$Server,k,pw1,pw2>), Out(senc(pw1,k)) ]

      /****ENDOFRULES****/

      /****RESTRICTIONS****/

      restriction OnlyOnce:
      	"All #i #j. OnlyOnce()@#i & OnlyOnce()@#j ==> #i = #j"

      /****LEMMAS****/

      lemma Executable: exists-trace
      	"Ex s x #i. Ack(s,x) @ #i"

      end

      /****ENDOFMODEL****/
      """;

  /**
   * Case (1): the user learns pw1 only from the server and does not retain it at User_1. The server
   * sends pw1 again, which User_2 receives and uses.
   */
  private static final String CASE1 = """
      /****MODEL****/
      theory ReacquisitionCase1

      begin

      builtins: symmetric-encryption

      /****RULES****/

      rule humansetup:
      	[ Fr(~k), Fr(~pw1), Fr(~pw2) ]
      	--[ OnlyOnce() ]->
      	[ !Type($User,'key',~k)
      	, !Type($User,'password',~pw1)
      	, !Type($User,'password',~pw2)
      	, !Init($User,$Server,~k,~pw1,~pw2)
      	]

      rule Setup:
      	[ !Init($User,$Server,k,pw1,pw2) ]
      	--[ Setup($User), Roles($User,$Server) ]->
      	[ State($User,'1',<$Server,k,pw2>), State($Server,'1',<$User,k,pw1>) ]

      rule Server_1:
      	[ State($Server,'1',<$User,k,pw1>) ]
      	--[ Issue($Server,pw1) ]->
      	[ State($Server,'2',<$User,k,pw1>), Out(pw1) ]

      rule User_1:
      	[ State($User,'1',<$Server,k,pw2>), In(pw1) ]
      	--[ H(), Receive($User,'c1',pw1), Forget(pw1), Send($User,'m1',senc('hi',k)), To($Server) ]->
      	[ State($User,'2',<$Server,k,pw1,pw2>), Out(senc('hi',k)) ]

      rule Server_2:
      	[ State($Server,'2',<$User,k,pw1>), In(senc('hi',k)) ]
      	--[ Hi($Server) ]->
      	[ State($Server,'3',<$User,k,pw1>), Out(pw1) ]

      rule User_2:
      	[ State($User,'2',<$Server,k,pw1,pw2>), In(pw1) ]
      	--[ H(), Receive($User,'c2',pw1), Send($User,'m2',senc(<'ack',pw1>,k)), To($Server) ]->
      	[ State($User,'3',<$Server,k,pw1,pw2>), Out(senc(<'ack',pw1>,k)) ]

      /****ENDOFRULES****/

      /****RESTRICTIONS****/

      restriction OnlyOnce:
      	"All #i #j. OnlyOnce()@#i & OnlyOnce()@#j ==> #i = #j"

      /****LEMMAS****/

      lemma Executable: exists-trace
      	"Ex s #i. Hi(s) @ #i"

      end

      /****ENDOFMODEL****/
      """;

  /** The control: the server sends 'reminder' instead of pw1, so pw1 is not received again. */
  private static String withoutReminder(String spec) {
    String control = spec
        .replace("Out(pw1) ]\n\nrule User_2", "Out('reminder') ]\n\nrule User_2")
        .replace("In(pw1) ]\n\t--[ H(), Receive($User,'c2',pw1)",
                 "In('reminder') ]\n\t--[ H(), Receive($User,'c2','reminder')");
    assertThat(control).contains("Receive($User,'c2','reminder')").contains("Out('reminder') ]");
    return control;
  }

  @Autowired private WebApplicationContext context;
  @Autowired private MutationWorkspace workspace;
  @Autowired private CeremonyVocabulary vocabulary;
  @Autowired private ForgetMutationStrategy strategy;

  private ForgetEndpointHarness harness;
  private CeremonyVocabulary savedVocabulary;

  @BeforeEach
  void setUp() {
    harness = new ForgetEndpointHarness(MockMvcBuilders.webAppContextSetup(context).build());
    savedVocabulary = new CeremonyVocabulary();
    savedVocabulary.copyFrom(vocabulary);
    vocabulary.copyFrom(new CeremonyVocabulary());
    strategy.setNonInternalActions(null);
  }

  @AfterEach
  void tearDown() throws IOException {
    vocabulary.copyFrom(savedVocabulary);
    try (Stream<Path> s = Files.list(workspace.root())) {
      for (Path p : s.toList()) {
        if (p.getFileName().toString().matches("Reacquisition\\w*_M\\d+\\.m")) Files.deleteIfExists(p);
      }
    }
  }

  /** Set {@code -Dxmen.forget.dump=<dir>} to keep the mutants and reports. */
  private String mutantOf(String name, String spec) throws Exception {
    ForgetEndpointHarness.Outcome o = harness.post(FORGET, name + ".spthy", spec);
    String dir = System.getProperty("xmen.forget.dump");
    if (dir != null) {
      Path d = Paths.get(dir, name);
      Files.createDirectories(d);
      for (Map.Entry<String, String> e : o.mutants().entrySet()) Files.writeString(d.resolve(e.getKey()), e.getValue());
      Files.writeString(d.resolve("report.txt"), o.report());
    }
    assertThat(o.status()).isEqualTo(200);
    return o.onlyMutant();
  }

  @Test
  @DisplayName("Case (2), control: pw1 is not received again, so User_2 and User_3 use pw2")
  void case2WithoutReminderTheLapsePersists() throws Exception {
    String m = mutantOf("ReacquisitionCase2Control", withoutReminder(CASE2));
    assertThat(ruleText(m, "User_2_M")).contains("Out(senc(<'ack',pw2>,k))");
    assertThat(ruleText(m, "User_3_M")).contains("Out(senc(pw2,k))");
  }

  @Test
  @DisplayName("Case (2): receiving pw1 again at User_2 restores pw1 at User_2 and User_3")
  void case2ReminderRestoresTheSends() throws Exception {
    String m = mutantOf("ReacquisitionCase2", CASE2);
    // Same step: the transition that receives pw1 again sends it, unchanged.
    assertThat(ruleText(m, "User_2")).startsWith("rule User_2:").contains("Out(senc(<'ack',pw1>,k))");
    // Later step: pw1 stays usable.
    assertThat(ruleText(m, "User_3")).startsWith("rule User_3:").contains("Out(senc(pw1,k))");
    assertThat(m).doesNotContain("rule User_2_M").doesNotContain("rule User_3_M");
  }

  @Test
  @DisplayName("Case (1), control: pw1 is not received again, so User_2 uses pw2")
  void case1WithoutReminderTheLapsePersists() throws Exception {
    String m = mutantOf("ReacquisitionCase1Control", withoutReminder(CASE1));
    assertThat(ruleText(m, "User_2_M")).contains("Out(senc(<'ack',pw2>,k))");
  }

  @Test
  @DisplayName("Case (1): receiving pw1 again at User_2 restores pw1 at User_2")
  void case1ReminderRestoresTheSend() throws Exception {
    String m = mutantOf("ReacquisitionCase1", CASE1);
    assertThat(ruleText(m, "User_2")).startsWith("rule User_2:").contains("Out(senc(<'ack',pw1>,k))");
    assertThat(m).doesNotContain("rule User_2_M");
  }
}
