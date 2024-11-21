package it.unive.lisa.cron;

import it.unive.lisa.AnalysisTestExecutor;
import it.unive.lisa.CronConfiguration;
import it.unive.lisa.DefaultConfiguration;
import it.unive.lisa.analysis.heap.TypeBasedHeap;
import it.unive.lisa.analysis.heap.pointbased.FieldSensitivePointBasedHeap;
import it.unive.lisa.analysis.heap.pointbased.PointBasedHeap;
import org.junit.Test;

public class MemoryAbstractionsTest extends AnalysisTestExecutor {

	@Test
	public void testTypeBasedHeap() {
		CronConfiguration conf = new CronConfiguration();
		conf.serializeResults = true;
		conf.abstractState = DefaultConfiguration.simpleState(
				new TypeBasedHeap(),
				DefaultConfiguration.defaultValueDomain(),
				DefaultConfiguration.defaultTypeDomain());
		conf.testDir = "heap";
		conf.testSubDir = "types";
		conf.programFile = "heap-type.imp";
		perform(conf);
	}

	@Test
	public void fieldInsensitivePointBasedHeapTest() {
		CronConfiguration conf = new CronConfiguration();
		conf.serializeResults = true;
		conf.abstractState = DefaultConfiguration.simpleState(
				new PointBasedHeap(),
				DefaultConfiguration.defaultValueDomain(),
				DefaultConfiguration.defaultTypeDomain());
		conf.testDir = "heap";
		conf.testSubDir = "pp";
		conf.programFile = "heap-pp.imp";
		perform(conf);
	}

	@Test
	public void fieldSensitivePointBasedHeapTest() {
		CronConfiguration conf = new CronConfiguration();
		conf.serializeResults = true;
		conf.abstractState = DefaultConfiguration.simpleState(
				new FieldSensitivePointBasedHeap(),
				DefaultConfiguration.defaultValueDomain(),
				DefaultConfiguration.defaultTypeDomain());
		conf.testDir = "heap";
		conf.testSubDir = "pp-field";
		conf.programFile = "heap-pp-field.imp";
		perform(conf);
	}
}
