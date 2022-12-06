import { builtinModules } from 'module';
import rollupTypescript from 'rollup-plugin-typescript2'

export default {
	input: 'email.ts',
	output: {
		file: 'email.js',
		format: 'es',
		sourcemap: true,
	},
	external: builtinModules,
	plugins: [
		rollupTypescript({ include: ['email.ts', 'smtp/*']  }),
	],
};

// removeComments: false, include: ['email.ts', 'smtp/*'] 
