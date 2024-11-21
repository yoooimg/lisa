package it.unive.lisa.cron;

import it.unive.lisa.AnalysisTestExecutor;
import it.unive.lisa.CronConfiguration;
import it.unive.lisa.DefaultConfiguration;
import it.unive.lisa.analysis.traces.TracePartitioning;
import org.junit.Test;

public class TracePartitioningTest extends AnalysisTestExecutor {

	@Test
	public void testTracePartitioning() {
		CronConfiguration conf = new CronConfiguration();
		conf.abstractState = new TracePartitioning<>(DefaultConfiguration.defaultAbstractState());
		conf.serializeResults = true;
		int prev = TracePartitioning.MAX_LOOP_ITERATIONS;
		TracePartitioning.MAX_LOOP_ITERATIONS = 3;
		conf.testDir = "traces";
		conf.programFile = "traces.imp";
		perform(conf);
		TracePartitioning.MAX_LOOP_ITERATIONS = prev;
	}
}
