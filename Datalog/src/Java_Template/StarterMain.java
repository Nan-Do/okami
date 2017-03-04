%% fill_Header

public class StarterMain {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		int num_threads = 1;
		Solver solver = new Solver();
		
		if (args.length == 1)
			num_threads = Integer.parseInt(args[0]);
		
		//System.out.println("Num Threads: " + num_threads);

		solver.init(num_threads);
		solver.compute();
		solver.end();
	}

}
